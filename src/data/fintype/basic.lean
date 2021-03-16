/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Finite types.
-/
import tactic.wlog
import data.finset.powerset
import data.finset.lattice
import data.finset.pi
import data.array.lemmas
import order.well_founded
import group_theory.perm.basic

open_locale nat

universes u v

variables {α : Type*} {β : Type*} {γ : Type*}

/-- `fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list. -/
class fintype (α : Type*) :=
(elems [] : finset α)
(complete : ∀ x : α, x ∈ elems)

namespace finset
variable [fintype α]

/-- `univ` is the universal finite set of type `finset α` implied from
  the assumption `fintype α`. -/
def univ : finset α := fintype.elems α

@[simp] theorem mem_univ (x : α) : x ∈ (univ : finset α) :=
fintype.complete x

@[simp] theorem mem_univ_val : ∀ x, x ∈ (univ : finset α).1 := mem_univ

@[simp] lemma coe_univ : ↑(univ : finset α) = (set.univ : set α) :=
by ext; simp

lemma univ_nonempty_iff : (univ : finset α).nonempty ↔ nonempty α :=
by rw [← coe_nonempty, coe_univ, set.nonempty_iff_univ_nonempty]

lemma univ_nonempty [nonempty α] : (univ : finset α).nonempty :=
univ_nonempty_iff.2 ‹_›

lemma univ_eq_empty : (univ : finset α) = ∅ ↔ ¬nonempty α :=
by rw [← univ_nonempty_iff, nonempty_iff_ne_empty, ne.def, not_not]

theorem subset_univ (s : finset α) : s ⊆ univ := λ a _, mem_univ a

instance : order_top (finset α) :=
{ top := univ,
  le_top := subset_univ,
  .. finset.partial_order }

instance [decidable_eq α] : boolean_algebra (finset α) :=
{ compl := λ s, univ \ s,
  sdiff_eq := λ s t, by simp [ext_iff],
  inf_compl_le_bot := λ s x hx, by simpa using hx,
  top_le_sup_compl := λ s x hx, by simp,
  ..finset.distrib_lattice,
  ..finset.semilattice_inf_bot,
  ..finset.order_top,
  ..finset.has_sdiff }

lemma compl_eq_univ_sdiff [decidable_eq α] (s : finset α) : sᶜ = univ \ s := rfl

@[simp] lemma mem_compl [decidable_eq α] {s : finset α} {x : α} : x ∈ sᶜ ↔ x ∉ s :=
by simp [compl_eq_univ_sdiff]

@[simp, norm_cast] lemma coe_compl [decidable_eq α] (s : finset α) : ↑(sᶜ) = (↑s : set α)ᶜ :=
set.ext $ λ x, mem_compl

@[simp] theorem union_compl [decidable_eq α] (s : finset α) : s ∪ sᶜ = finset.univ :=
sup_compl_eq_top

@[simp] lemma compl_filter [decidable_eq α] (p : α → Prop) [decidable_pred p]
  [Π x, decidable (¬p x)] :
  (univ.filter p)ᶜ = univ.filter (λ x, ¬p x) :=
(filter_not _ _).symm

theorem eq_univ_iff_forall {s : finset α} : s = univ ↔ ∀ x, x ∈ s :=
by simp [ext_iff]

lemma compl_ne_univ_iff_nonempty [decidable_eq α] (s : finset α) : sᶜ ≠ univ ↔ s.nonempty :=
by simp [eq_univ_iff_forall, finset.nonempty]

@[simp] lemma univ_inter [decidable_eq α] (s : finset α) :
  univ ∩ s = s := ext $ λ a, by simp

@[simp] lemma inter_univ [decidable_eq α] (s : finset α) :
  s ∩ univ = s :=
by rw [inter_comm, univ_inter]

@[simp] lemma piecewise_univ [∀i : α, decidable (i ∈ (univ : finset α))]
  {δ : α → Sort*} (f g : Πi, δ i) : univ.piecewise f g = f :=
by { ext i, simp [piecewise] }

lemma piecewise_compl [decidable_eq α] (s : finset α) [Π i : α, decidable (i ∈ s)]
  [Π i : α, decidable (i ∈ sᶜ)] {δ : α → Sort*} (f g : Π i, δ i) :
  sᶜ.piecewise f g = s.piecewise g f :=
by { ext i, simp [piecewise] }

lemma univ_map_equiv_to_embedding {α β : Type*} [fintype α] [fintype β] (e : α ≃ β) :
  univ.map e.to_embedding = univ :=
begin
  apply eq_univ_iff_forall.mpr,
  intro b,
  rw [mem_map],
  use e.symm b,
  simp,
end

@[simp] lemma univ_filter_exists (f : α → β) [fintype β]
  [decidable_pred (λ y, ∃ x, f x = y)] [decidable_eq β] :
  finset.univ.filter (λ y, ∃ x, f x = y) = finset.univ.image f :=
by { ext, simp }

/-- Note this is a special case of `(finset.image_preimage f univ _).symm`. -/
lemma univ_filter_mem_range (f : α → β) [fintype β]
  [decidable_pred (λ y, y ∈ set.range f)] [decidable_eq β] :
  finset.univ.filter (λ y, y ∈ set.range f) = finset.univ.image f :=
univ_filter_exists f

end finset

open finset function

namespace fintype

instance decidable_pi_fintype {α} {β : α → Type*} [∀a, decidable_eq (β a)] [fintype α] :
  decidable_eq (Πa, β a) :=
assume f g, decidable_of_iff (∀ a ∈ fintype.elems α, f a = g a)
  (by simp [function.funext_iff, fintype.complete])

instance decidable_forall_fintype {p : α → Prop} [decidable_pred p] [fintype α] :
  decidable (∀ a, p a) :=
decidable_of_iff (∀ a ∈ @univ α _, p a) (by simp)

instance decidable_exists_fintype {p : α → Prop} [decidable_pred p] [fintype α] :
  decidable (∃ a, p a) :=
decidable_of_iff (∃ a ∈ @univ α _, p a) (by simp)

instance decidable_eq_equiv_fintype [decidable_eq β] [fintype α] :
  decidable_eq (α ≃ β) :=
λ a b, decidable_of_iff (a.1 = b.1) ⟨λ h, equiv.ext (congr_fun h), congr_arg _⟩

instance decidable_injective_fintype [decidable_eq α] [decidable_eq β] [fintype α] :
  decidable_pred (injective : (α → β) → Prop) := λ x, by unfold injective; apply_instance

instance decidable_surjective_fintype [decidable_eq β] [fintype α] [fintype β] :
  decidable_pred (surjective : (α → β) → Prop) := λ x, by unfold surjective; apply_instance

instance decidable_bijective_fintype [decidable_eq α] [decidable_eq β] [fintype α] [fintype β] :
  decidable_pred (bijective : (α → β) → Prop) := λ x, by unfold bijective; apply_instance

instance decidable_left_inverse_fintype [decidable_eq α] [fintype α] (f : α → β) (g : β → α) :
  decidable (function.right_inverse f g) :=
show decidable (∀ x, g (f x) = x), by apply_instance

instance decidable_right_inverse_fintype [decidable_eq β] [fintype β] (f : α → β) (g : β → α) :
  decidable (function.left_inverse f g) :=
show decidable (∀ x, f (g x) = x), by apply_instance

/-- Construct a proof of `fintype α` from a universal multiset -/
def of_multiset [decidable_eq α] (s : multiset α)
  (H : ∀ x : α, x ∈ s) : fintype α :=
⟨s.to_finset, by simpa using H⟩

/-- Construct a proof of `fintype α` from a universal list -/
def of_list [decidable_eq α] (l : list α)
  (H : ∀ x : α, x ∈ l) : fintype α :=
⟨l.to_finset, by simpa using H⟩

theorem exists_univ_list (α) [fintype α] :
  ∃ l : list α, l.nodup ∧ ∀ x : α, x ∈ l :=
let ⟨l, e⟩ := quotient.exists_rep (@univ α _).1 in
by have := and.intro univ.2 mem_univ_val;
   exact ⟨_, by rwa ← e at this⟩

/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [fintype α] : ℕ := (@univ α _).card

/-- If `l` lists all the elements of `α` without duplicates, then `α ≃ fin (l.length)`. -/
def equiv_fin_of_forall_mem_list {α} [decidable_eq α]
  {l : list α} (h : ∀ x:α, x ∈ l) (nd : l.nodup) : α ≃ fin (l.length) :=
⟨λ a, ⟨_, list.index_of_lt_length.2 (h a)⟩,
 λ i, l.nth_le i.1 i.2,
 λ a, by simp,
 λ ⟨i, h⟩, fin.eq_of_veq $ list.nodup_iff_nth_le_inj.1 nd _ _
   (list.index_of_lt_length.2 (list.nth_le_mem _ _ _)) h $ by simp⟩

/-- There is (computably) a bijection between `α` and `fin n` where
  `n = card α`. Since it is not unique, and depends on which permutation
  of the universe list is used, the bijection is wrapped in `trunc` to
  preserve computability.  -/
def equiv_fin (α) [decidable_eq α] [fintype α] : trunc (α ≃ fin (card α)) :=
by unfold card finset.card; exact
quot.rec_on_subsingleton (@univ α _).1
  (λ l (h : ∀ x:α, x ∈ l) (nd : l.nodup), trunc.mk (equiv_fin_of_forall_mem_list h nd))
  mem_univ_val univ.2

theorem exists_equiv_fin (α) [fintype α] : ∃ n, nonempty (α ≃ fin n) :=
by haveI := classical.dec_eq α; exact ⟨card α, nonempty_of_trunc (equiv_fin α)⟩

instance (α : Type*) : subsingleton (fintype α) :=
⟨λ ⟨s₁, h₁⟩ ⟨s₂, h₂⟩, by congr; simp [finset.ext_iff, h₁, h₂]⟩

/-- Given a predicate that can be represented by a finset, the subtype
associated to the predicate is a fintype. -/
protected def subtype {p : α → Prop} (s : finset α)
  (H : ∀ x : α, x ∈ s ↔ p x) : fintype {x // p x} :=
⟨⟨multiset.pmap subtype.mk s.1 (λ x, (H x).1),
  multiset.nodup_pmap (λ a _ b _, congr_arg subtype.val) s.2⟩,
λ ⟨x, px⟩, multiset.mem_pmap.2 ⟨x, (H x).2 px, rfl⟩⟩

theorem subtype_card {p : α → Prop} (s : finset α)
  (H : ∀ x : α, x ∈ s ↔ p x) :
  @card {x // p x} (fintype.subtype s H) = s.card :=
multiset.card_pmap _ _ _

theorem card_of_subtype {p : α → Prop} (s : finset α)
  (H : ∀ x : α, x ∈ s ↔ p x) [fintype {x // p x}] :
  card {x // p x} = s.card :=
by { rw ← subtype_card s H, congr }

/-- Construct a fintype from a finset with the same elements. -/
def of_finset {p : set α} (s : finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : fintype p :=
fintype.subtype s H

@[simp] theorem card_of_finset {p : set α} (s : finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) :
  @fintype.card p (of_finset s H) = s.card :=
fintype.subtype_card s H

theorem card_of_finset' {p : set α} (s : finset α)
  (H : ∀ x, x ∈ s ↔ x ∈ p) [fintype p] : fintype.card p = s.card :=
by rw ← card_of_finset s H; congr

/-- If `f : α → β` is a bijection and `α` is a fintype, then `β` is also a fintype. -/
def of_bijective [fintype α] (f : α → β) (H : function.bijective f) : fintype β :=
⟨univ.map ⟨f, H.1⟩,
λ b, let ⟨a, e⟩ := H.2 b in e ▸ mem_map_of_mem _ (mem_univ _)⟩

/-- If `f : α → β` is a surjection and `α` is a fintype, then `β` is also a fintype. -/
def of_surjective [decidable_eq β] [fintype α] (f : α → β) (H : function.surjective f) :
  fintype β :=
⟨univ.image f, λ b, let ⟨a, e⟩ := H b in e ▸ mem_image_of_mem _ (mem_univ _)⟩

end fintype

section inv

namespace function

variables [fintype α] [decidable_eq β]

namespace injective

variables {f : α → β} (hf : function.injective f)

/--
The inverse of an `hf : injective` function `f : α → β`, of the type `↥(set.range f) → α`.
This is the computable version of `function.inv_fun` that requires `fintype α` and `decidable_eq β`,
or the function version of applying `(equiv.set.range f hf).symm`.
This function should not usually be used for actual computation because for most cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so it is O(N) where
`N = fintype.card α`.
-/
def inv_of_mem_range : set.range f → α :=
λ b, finset.choose (λ a, f a = b) finset.univ ((exists_unique_congr (by simp)).mp
  (hf.exists_unique_of_mem_range b.property))

lemma left_inv_of_inv_of_mem_range (b : set.range f) :
  f (hf.inv_of_mem_range b) = b :=
(finset.choose_spec (λ a, f a = b) _ _).right

@[simp] lemma right_inv_of_inv_of_mem_range (a : α) :
  hf.inv_of_mem_range (⟨f a, set.mem_range_self a⟩) = a :=
hf (finset.choose_spec (λ a', f a' = f a) _ _).right

lemma inv_fun_restrict [nonempty α] :
  (set.range f).restrict (inv_fun f) = hf.inv_of_mem_range :=
begin
  ext ⟨b, h⟩,
  apply hf,
  simp [hf.left_inv_of_inv_of_mem_range, @inv_fun_eq _ _ _ f b (set.mem_range.mp h)]
end

lemma inv_of_mem_range_surjective : function.surjective hf.inv_of_mem_range :=
λ a, ⟨⟨f a, set.mem_range_self a⟩, by simp⟩

end injective

namespace embedding

variables (f : α ↪ β) (b : set.range f)

/--
The inverse of an embedding `f : α ↪ β`, of the type `↥(set.range f) → α`.
This is the computable version of `function.inv_fun` that requires `fintype α` and `decidable_eq β`,
or the function version of applying `(equiv.set.range f f.injective).symm`.
This function should not usually be used for actual computation because for most cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so it is O(N) where
`N = fintype.card α`.
-/
def inv_of_mem_range : α :=
f.injective.inv_of_mem_range b

@[simp] lemma left_inv_of_inv_of_mem_range :
  f (f.inv_of_mem_range b) = b :=
f.injective.left_inv_of_inv_of_mem_range b

@[simp] lemma right_inv_of_inv_of_mem_range (a : α) :
  f.inv_of_mem_range ⟨f a, set.mem_range_self a⟩ = a :=
f.injective.right_inv_of_inv_of_mem_range a

lemma inv_fun_restrict [nonempty α] :
  (set.range f).restrict (inv_fun f) = f.inv_of_mem_range :=
begin
  ext ⟨b, h⟩,
  apply f.injective,
  simp [f.left_inv_of_inv_of_mem_range, @inv_fun_eq _ _ _ f b (set.mem_range.mp h)]
end

lemma inv_of_mem_range_surjective : function.surjective f.inv_of_mem_range :=
λ a, ⟨⟨f a, set.mem_range_self a⟩, by simp⟩

end embedding

end function

end inv

namespace fintype

/-- Given an injective function to a fintype, the domain is also a
fintype. This is noncomputable because injectivity alone cannot be
used to construct preimages. -/
noncomputable def of_injective [fintype β] (f : α → β) (H : function.injective f) : fintype α :=
by letI := classical.dec; exact
if hα : nonempty α then by letI := classical.inhabited_of_nonempty hα;
  exact of_surjective (inv_fun f) (inv_fun_surjective H)
else ⟨∅, λ x, (hα ⟨x⟩).elim⟩

/-- If `f : α ≃ β` and `α` is a fintype, then `β` is also a fintype. -/
def of_equiv (α : Type*) [fintype α] (f : α ≃ β) : fintype β := of_bijective _ f.bijective

theorem of_equiv_card [fintype α] (f : α ≃ β) :
  @card β (of_equiv α f) = card α :=
multiset.card_map _ _

theorem card_congr {α β} [fintype α] [fintype β] (f : α ≃ β) : card α = card β :=
by rw ← of_equiv_card f; congr

theorem card_eq {α β} [F : fintype α] [G : fintype β] : card α = card β ↔ nonempty (α ≃ β) :=
⟨λ h, ⟨by classical;
  calc α ≃ fin (card α) : trunc.out (equiv_fin α)
     ... ≃ fin (card β) : by rw h
     ... ≃ β : (trunc.out (equiv_fin β)).symm⟩,
λ ⟨f⟩, card_congr f⟩

/-- Subsingleton types are fintypes (with zero or one terms). -/
def of_subsingleton (a : α) [subsingleton α] : fintype α :=
⟨{a}, λ b, finset.mem_singleton.2 (subsingleton.elim _ _)⟩

@[simp] theorem univ_of_subsingleton (a : α) [subsingleton α] :
  @univ _ (of_subsingleton a) = {a} := rfl

@[simp] theorem card_of_subsingleton (a : α) [subsingleton α] :
  @fintype.card _ (of_subsingleton a) = 1 := rfl

end fintype

namespace set

/-- Construct a finset enumerating a set `s`, given a `fintype` instance.  -/
def to_finset (s : set α) [fintype s] : finset α :=
⟨(@finset.univ s _).1.map subtype.val,
 multiset.nodup_map (λ a b, subtype.eq) finset.univ.2⟩

@[simp] theorem mem_to_finset {s : set α} [fintype s] {a : α} : a ∈ s.to_finset ↔ a ∈ s :=
by simp [to_finset]

@[simp] theorem mem_to_finset_val {s : set α} [fintype s] {a : α} : a ∈ s.to_finset.1 ↔ a ∈ s :=
mem_to_finset

-- We use an arbitrary `[fintype s]` instance here,
-- not necessarily coming from a `[fintype α]`.
@[simp]
lemma to_finset_card {α : Type*} (s : set α) [fintype s] :
  s.to_finset.card = fintype.card s :=
multiset.card_map subtype.val finset.univ.val

@[simp] theorem coe_to_finset (s : set α) [fintype s] : (↑s.to_finset : set α) = s :=
set.ext $ λ _, mem_to_finset

@[simp] theorem to_finset_inj {s t : set α} [fintype s] [fintype t] :
  s.to_finset = t.to_finset ↔ s = t :=
⟨λ h, by rw [← s.coe_to_finset, h, t.coe_to_finset], λ h, by simp [h]; congr⟩

end set

lemma finset.card_univ [fintype α] : (finset.univ : finset α).card = fintype.card α :=
rfl

lemma finset.eq_univ_of_card [fintype α] (s : finset α) (hs : s.card = fintype.card α) :
  s = univ :=
eq_of_subset_of_card_le (subset_univ _) $ by rw [hs, finset.card_univ]

lemma finset.card_eq_iff_eq_univ [fintype α] (s : finset α) :
  s.card = fintype.card α ↔ s = finset.univ :=
⟨s.eq_univ_of_card, by { rintro rfl, exact finset.card_univ, }⟩

lemma finset.card_le_univ [fintype α] (s : finset α) :
  s.card ≤ fintype.card α :=
card_le_of_subset (subset_univ s)

lemma finset.card_lt_univ_of_not_mem [fintype α] {s : finset α} {x : α} (hx : x ∉ s) :
  s.card < fintype.card α :=
card_lt_card ⟨subset_univ s, not_forall.2 ⟨x, λ hx', hx (hx' $ mem_univ x)⟩⟩

lemma finset.card_lt_iff_ne_univ [fintype α] (s : finset α) :
  s.card < fintype.card α ↔ s ≠ finset.univ :=
s.card_le_univ.lt_iff_ne.trans (not_iff_not_of_iff s.card_eq_iff_eq_univ)

lemma finset.card_compl_lt_iff_nonempty [fintype α] [decidable_eq α] (s : finset α) :
  sᶜ.card < fintype.card α ↔ s.nonempty :=
sᶜ.card_lt_iff_ne_univ.trans s.compl_ne_univ_iff_nonempty

lemma finset.card_univ_diff [decidable_eq α] [fintype α] (s : finset α) :
  (finset.univ \ s).card = fintype.card α - s.card :=
finset.card_sdiff (subset_univ s)

lemma finset.card_compl [decidable_eq α] [fintype α] (s : finset α) :
  sᶜ.card = fintype.card α - s.card :=
finset.card_univ_diff s

instance (n : ℕ) : fintype (fin n) :=
⟨finset.fin_range n, finset.mem_fin_range⟩

lemma fin.univ_def (n : ℕ) : (univ : finset (fin n)) = finset.fin_range n := rfl

@[simp] theorem fintype.card_fin (n : ℕ) : fintype.card (fin n) = n :=
list.length_fin_range n

@[simp] lemma finset.card_fin (n : ℕ) : finset.card (finset.univ : finset (fin n)) = n :=
by rw [finset.card_univ, fintype.card_fin]

lemma fin.equiv_iff_eq {m n : ℕ} : nonempty (fin m ≃ fin n) ↔ m = n :=
  ⟨λ ⟨h⟩, by simpa using fintype.card_congr h, λ h, ⟨equiv.cast $ h ▸ rfl ⟩ ⟩

/-- Embed `fin n` into `fin (n + 1)` by prepending zero to the `univ` -/
lemma fin.univ_succ (n : ℕ) :
  (univ : finset (fin (n + 1))) = insert 0 (univ.image fin.succ) :=
begin
  ext m,
  simp only [mem_univ, mem_insert, true_iff, mem_image, exists_prop],
  exact fin.cases (or.inl rfl) (λ i, or.inr ⟨i, trivial, rfl⟩) m
end

/-- Embed `fin n` into `fin (n + 1)` by appending a new `fin.last n` to the `univ` -/
lemma fin.univ_cast_succ (n : ℕ) :
  (univ : finset (fin (n + 1))) = insert (fin.last n) (univ.image fin.cast_succ) :=
begin
  ext m,
  simp only [mem_univ, mem_insert, true_iff, mem_image, exists_prop, true_and],
  by_cases h : m.val < n,
  { right,
    use fin.cast_lt m h,
    rw fin.cast_succ_cast_lt },
  { left,
    exact fin.eq_last_of_not_lt h }
end

/-- Embed `fin n` into `fin (n + 1)` by inserting
around a specified pivot `p : fin (n + 1)` into the `univ` -/
lemma fin.univ_succ_above (n : ℕ) (p : fin (n + 1)) :
  (univ : finset (fin (n + 1))) = insert p (univ.image (fin.succ_above p)) :=
begin
  rcases lt_or_eq_of_le (fin.le_last p) with hl|rfl,
  { ext m,
    simp only [finset.mem_univ, finset.mem_insert, true_iff, finset.mem_image, exists_prop],
    refine or_iff_not_imp_left.mpr _,
    { intro h,
      cases n,
      { have : m = p := by simp,
        exact absurd this h },
      use p.cast_pred.pred_above m,
      { rw fin.pred_above,
        split_ifs with H,
        { simp only [fin.coe_cast_succ, true_and, fin.coe_coe_eq_self, coe_coe],
          rw fin.lt_last_iff_coe_cast_pred at hl,
          rw fin.succ_above_above,
          { simp },
          { simp only [fin.lt_iff_coe_lt_coe, fin.coe_cast_succ] at H,
            simpa [fin.le_iff_coe_le_coe, ←hl] using nat.le_pred_of_lt H } },
        { rw fin.succ_above_below,
          { simp },
          { simp only [fin.cast_succ_cast_pred hl, not_lt] at H,
            simpa using lt_of_le_of_ne H h, } } } } },
  { rw fin.succ_above_last,
    exact fin.univ_cast_succ n }
end

@[instance, priority 10] def unique.fintype {α : Type*} [unique α] : fintype α :=
fintype.of_subsingleton (default α)

@[simp] lemma univ_unique {α : Type*} [unique α] [f : fintype α] : @finset.univ α _ = {default α} :=
by rw [subsingleton.elim f (@unique.fintype α _)]; refl

instance : fintype empty := ⟨∅, empty.rec _⟩

@[simp] theorem fintype.univ_empty : @univ empty _ = ∅ := rfl

@[simp] theorem fintype.card_empty : fintype.card empty = 0 := rfl

instance : fintype pempty := ⟨∅, pempty.rec _⟩

@[simp] theorem fintype.univ_pempty : @univ pempty _ = ∅ := rfl

@[simp] theorem fintype.card_pempty : fintype.card pempty = 0 := rfl

instance : fintype unit := fintype.of_subsingleton ()

theorem fintype.univ_unit : @univ unit _ = {()} := rfl

theorem fintype.card_unit : fintype.card unit = 1 := rfl

instance : fintype punit := fintype.of_subsingleton punit.star

@[simp] theorem fintype.univ_punit : @univ punit _ = {punit.star} := rfl

@[simp] theorem fintype.card_punit : fintype.card punit = 1 := rfl

instance : fintype bool := ⟨⟨tt ::ₘ ff ::ₘ 0, by simp⟩, λ x, by cases x; simp⟩

@[simp] theorem fintype.univ_bool : @univ bool _ = {tt, ff} := rfl

instance units_int.fintype : fintype (units ℤ) :=
⟨{1, -1}, λ x, by cases int.units_eq_one_or x; simp *⟩

instance additive.fintype [fintype α] : fintype (additive α) :=
fintype.of_equiv α additive.of_mul

instance multiplicative.fintype [fintype α] : fintype (multiplicative α) :=
fintype.of_equiv α multiplicative.of_add

@[simp] lemma fintype.card_additive [fintype α] :
  fintype.card (additive α) = fintype.card α :=
fintype.card_congr additive.to_mul

@[simp] lemma fintype.card_multiplicative [fintype α] :
  fintype.card (multiplicative α) = fintype.card α :=
fintype.card_congr multiplicative.to_add

@[simp] theorem fintype.card_units_int : fintype.card (units ℤ) = 2 := rfl

noncomputable instance [monoid α] [fintype α] : fintype (units α) :=
by classical; exact fintype.of_injective units.val units.ext

@[simp] theorem fintype.card_bool : fintype.card bool = 2 := rfl

/-- Given a finset on `α`, lift it to being a finset on `option α`
using `option.some` and then insert `option.none`. -/
def finset.insert_none (s : finset α) : finset (option α) :=
⟨none ::ₘ s.1.map some, multiset.nodup_cons.2
  ⟨by simp, multiset.nodup_map (λ a b, option.some.inj) s.2⟩⟩

@[simp] theorem finset.mem_insert_none {s : finset α} : ∀ {o : option α},
  o ∈ s.insert_none ↔ ∀ a ∈ o, a ∈ s
| none     := iff_of_true (multiset.mem_cons_self _ _) (λ a h, by cases h)
| (some a) := multiset.mem_cons.trans $ by simp; refl

theorem finset.some_mem_insert_none {s : finset α} {a : α} :
  some a ∈ s.insert_none ↔ a ∈ s := by simp

instance {α : Type*} [fintype α] : fintype (option α) :=
⟨univ.insert_none, λ a, by simp⟩

@[simp] theorem fintype.card_option {α : Type*} [fintype α] :
  fintype.card (option α) = fintype.card α + 1 :=
(multiset.card_cons _ _).trans (by rw multiset.card_map; refl)

instance {α : Type*} (β : α → Type*)
  [fintype α] [∀ a, fintype (β a)] : fintype (sigma β) :=
⟨univ.sigma (λ _, univ), λ ⟨a, b⟩, by simp⟩

@[simp] lemma finset.univ_sigma_univ {α : Type*} {β : α → Type*} [fintype α] [∀ a, fintype (β a)] :
  (univ : finset α).sigma (λ a, (univ : finset (β a))) = univ := rfl

instance (α β : Type*) [fintype α] [fintype β] : fintype (α × β) :=
⟨univ.product univ, λ ⟨a, b⟩, by simp⟩

@[simp] lemma finset.univ_product_univ {α β : Type*} [fintype α] [fintype β] :
  (univ : finset α).product (univ : finset β) = univ :=
rfl

@[simp] theorem fintype.card_prod (α β : Type*) [fintype α] [fintype β] :
  fintype.card (α × β) = fintype.card α * fintype.card β :=
card_product _ _

/-- Given that `α × β` is a fintype, `α` is also a fintype. -/
def fintype.fintype_prod_left {α β} [decidable_eq α] [fintype (α × β)] [nonempty β] : fintype α :=
⟨(fintype.elems (α × β)).image prod.fst,
  assume a, let ⟨b⟩ := ‹nonempty β› in by simp; exact ⟨b, fintype.complete _⟩⟩

/-- Given that `α × β` is a fintype, `β` is also a fintype. -/
def fintype.fintype_prod_right {α β} [decidable_eq β] [fintype (α × β)] [nonempty α] : fintype β :=
⟨(fintype.elems (α × β)).image prod.snd,
  assume b, let ⟨a⟩ := ‹nonempty α› in by simp; exact ⟨a, fintype.complete _⟩⟩

instance (α : Type*) [fintype α] : fintype (ulift α) :=
fintype.of_equiv _ equiv.ulift.symm

@[simp] theorem fintype.card_ulift (α : Type*) [fintype α] :
  fintype.card (ulift α) = fintype.card α :=
fintype.of_equiv_card _

lemma univ_sum_type {α β : Type*} [fintype α] [fintype β] [fintype (α ⊕ β)] [decidable_eq (α ⊕ β)] :
  (univ : finset (α ⊕ β)) = map function.embedding.inl univ ∪ map function.embedding.inr univ :=
begin
  rw [eq_comm, eq_univ_iff_forall], simp only [mem_union, mem_map, exists_prop, mem_univ, true_and],
  rintro (x|y), exacts [or.inl ⟨x, rfl⟩, or.inr ⟨y, rfl⟩]
end

instance (α : Type u) (β : Type v) [fintype α] [fintype β] : fintype (α ⊕ β) :=
@fintype.of_equiv _ _ (@sigma.fintype _
    (λ b, cond b (ulift α) (ulift.{(max u v) v} β)) _
    (λ b, by cases b; apply ulift.fintype))
  ((equiv.sum_equiv_sigma_bool _ _).symm.trans
    (equiv.sum_congr equiv.ulift equiv.ulift))

namespace fintype
variables [fintype α] [fintype β]

lemma card_le_of_injective (f : α → β) (hf : function.injective f) : card α ≤ card β :=
finset.card_le_card_of_inj_on f (λ _ _, finset.mem_univ _) (λ _ _ _ _ h, hf h)

lemma card_le_of_embedding (f : α ↪ β) : card α ≤ card β := card_le_of_injective f f.2

lemma card_lt_of_injective_of_not_mem (f : α → β) (h : function.injective f)
  {b : β} (w : b ∉ set.range f) : fintype.card α < fintype.card β :=
calc card α = (univ.map ⟨f, h⟩).card : (card_map _).symm
... < card β : finset.card_lt_univ_of_not_mem $
                 by rwa [← mem_coe, coe_map, coe_univ, set.image_univ]

lemma card_lt_of_injective_not_surjective (f : α → β) (h : function.injective f)
  (h' : ¬function.surjective f) : fintype.card α < fintype.card β :=
let ⟨y, hy⟩ := not_forall.1 h' in card_lt_of_injective_of_not_mem f h hy

/--
The pigeonhole principle for finitely many pigeons and pigeonholes.
This is the `fintype` version of `finset.exists_ne_map_eq_of_card_lt_of_maps_to`.
-/
lemma exists_ne_map_eq_of_card_lt (f : α → β) (h : fintype.card β < fintype.card α) :
  ∃ x y, x ≠ y ∧ f x = f y :=
let ⟨x, _, y, _, h⟩ := finset.exists_ne_map_eq_of_card_lt_of_maps_to h (λ x _, mem_univ (f x))
in ⟨x, y, h⟩

lemma card_eq_one_iff : card α = 1 ↔ (∃ x : α, ∀ y, y = x) :=
by rw [← card_unit, card_eq]; exact
⟨λ ⟨a⟩, ⟨a.symm (), λ y, a.injective (subsingleton.elim _ _)⟩,
  λ ⟨x, hx⟩, ⟨⟨λ _, (), λ _, x, λ _, (hx _).trans (hx _).symm,
    λ _, subsingleton.elim _ _⟩⟩⟩

lemma card_eq_zero_iff : card α = 0 ↔ (α → false) :=
⟨λ h a, have e : α ≃ empty := classical.choice (card_eq.1 (by simp [h])), (e a).elim,
  λ h, have e : α ≃ empty := ⟨λ a, (h a).elim, λ a, a.elim, λ a, (h a).elim, λ a, a.elim⟩,
    by simp [card_congr e]⟩

/-- A `fintype` with cardinality zero is (constructively) equivalent to `pempty`. -/
def card_eq_zero_equiv_equiv_pempty :
  card α = 0 ≃ (α ≃ pempty.{v+1}) :=
{ to_fun := λ h,
  { to_fun := λ a, false.elim (card_eq_zero_iff.1 h a),
    inv_fun := λ a, pempty.elim a,
    left_inv := λ a, false.elim (card_eq_zero_iff.1 h a),
    right_inv := λ a, pempty.elim a, },
  inv_fun := λ e,
  by { simp only [←of_equiv_card e], convert card_pempty, },
  left_inv := λ h, rfl,
  right_inv := λ e, by { ext x, cases e x, } }

lemma card_pos_iff : 0 < card α ↔ nonempty α :=
⟨λ h, classical.by_contradiction (λ h₁,
  have card α = 0 := card_eq_zero_iff.2 (λ a, h₁ ⟨a⟩),
  lt_irrefl 0 $ by rwa this at h),
λ ⟨a⟩, nat.pos_of_ne_zero (mt card_eq_zero_iff.1 (λ h, h a))⟩

lemma card_le_one_iff : card α ≤ 1 ↔ (∀ a b : α, a = b) :=
let n := card α in
have hn : n = card α := rfl,
match n, hn with
| 0 := λ ha, ⟨λ h, λ a, (card_eq_zero_iff.1 ha.symm a).elim, λ _, ha ▸ nat.le_succ _⟩
| 1 := λ ha, ⟨λ h, λ a b, let ⟨x, hx⟩ := card_eq_one_iff.1 ha.symm in
  by rw [hx a, hx b],
    λ _, ha ▸ le_refl _⟩
| (n+2) := λ ha, ⟨λ h, by rw ← ha at h; exact absurd h dec_trivial,
  (λ h, card_unit ▸ card_le_of_injective (λ _, ())
    (λ _ _ _, h _ _))⟩
end

lemma card_le_one_iff_subsingleton : card α ≤ 1 ↔ subsingleton α :=
iff.trans card_le_one_iff subsingleton_iff.symm

lemma one_lt_card_iff_nontrivial : 1 < card α ↔ nontrivial α :=
begin
  classical,
  rw ← not_iff_not,
  push_neg,
  rw [not_nontrivial_iff_subsingleton, card_le_one_iff_subsingleton]
end

lemma exists_ne_of_one_lt_card (h : 1 < card α) (a : α) : ∃ b : α, b ≠ a :=
by { haveI : nontrivial α := one_lt_card_iff_nontrivial.1 h, exact exists_ne a }

lemma exists_pair_of_one_lt_card (h : 1 < card α) : ∃ (a b : α), a ≠ b :=
by { haveI : nontrivial α := one_lt_card_iff_nontrivial.1 h, exact exists_pair_ne α }

lemma card_eq_one_of_forall_eq {i : α} (h : ∀ j, j = i) : card α = 1 :=
fintype.card_eq_one_iff.2 ⟨i,h⟩

lemma injective_iff_surjective {f : α → α} : injective f ↔ surjective f :=
by haveI := classical.prop_decidable; exact
have ∀ {f : α → α}, injective f → surjective f,
from λ f hinj x,
  have h₁ : image f univ = univ := eq_of_subset_of_card_le (subset_univ _)
    ((card_image_of_injective univ hinj).symm ▸ le_refl _),
  have h₂ : x ∈ image f univ := h₁.symm ▸ mem_univ _,
  exists_of_bex (mem_image.1 h₂),
⟨this,
  λ hsurj, has_left_inverse.injective
    ⟨surj_inv hsurj, left_inverse_of_surjective_of_right_inverse
      (this (injective_surj_inv _)) (right_inverse_surj_inv _)⟩⟩

lemma injective_iff_bijective {f : α → α} : injective f ↔ bijective f :=
by simp [bijective, injective_iff_surjective]

lemma surjective_iff_bijective {f : α → α} : surjective f ↔ bijective f :=
by simp [bijective, injective_iff_surjective]

lemma injective_iff_surjective_of_equiv {β : Type*} {f : α → β} (e : α ≃ β) :
  injective f ↔ surjective f :=
have injective (e.symm ∘ f) ↔ surjective (e.symm ∘ f), from injective_iff_surjective,
⟨λ hinj, by simpa [function.comp] using
  e.surjective.comp (this.1 (e.symm.injective.comp hinj)),
λ hsurj, by simpa [function.comp] using
  e.injective.comp (this.2 (e.symm.surjective.comp hsurj))⟩

lemma nonempty_equiv_of_card_eq (h : card α = card β) :
  nonempty (α ≃ β) :=
begin
  obtain ⟨m, ⟨f⟩⟩ := exists_equiv_fin α,
  obtain ⟨n, ⟨g⟩⟩ := exists_equiv_fin β,
  suffices : m = n,
  { subst this, exact ⟨f.trans g.symm⟩ },
  calc m = card (fin m) : (card_fin m).symm
     ... = card α       : card_congr f.symm
     ... = card β       : h
     ... = card (fin n) : card_congr g
     ... = n            : card_fin n
end

lemma bijective_iff_injective_and_card (f : α → β) :
  bijective f ↔ injective f ∧ card α = card β :=
begin
  split,
  { intro h, exact ⟨h.1, card_congr (equiv.of_bijective f h)⟩ },
  { rintro ⟨hf, h⟩,
    refine ⟨hf, _⟩,
    obtain ⟨e⟩ : nonempty (α ≃ β) := nonempty_equiv_of_card_eq h,
    rwa ← injective_iff_surjective_of_equiv e }
end

lemma bijective_iff_surjective_and_card (f : α → β) :
  bijective f ↔ surjective f ∧ card α = card β :=
begin
  split,
  { intro h, exact ⟨h.2, card_congr (equiv.of_bijective f h)⟩, },
  { rintro ⟨hf, h⟩,
    refine ⟨_, hf⟩,
    obtain ⟨e⟩ : nonempty (α ≃ β) := nonempty_equiv_of_card_eq h,
    rwa injective_iff_surjective_of_equiv e }
end

end fintype

lemma fintype.coe_image_univ [fintype α] [decidable_eq β] {f : α → β} :
  ↑(finset.image f finset.univ) = set.range f :=
by { ext x, simp }

instance list.subtype.fintype [decidable_eq α] (l : list α) : fintype {x // x ∈ l} :=
fintype.of_list l.attach l.mem_attach

instance multiset.subtype.fintype [decidable_eq α] (s : multiset α) : fintype {x // x ∈ s} :=
fintype.of_multiset s.attach s.mem_attach

instance finset.subtype.fintype (s : finset α) : fintype {x // x ∈ s} :=
⟨s.attach, s.mem_attach⟩

instance finset_coe.fintype (s : finset α) : fintype (↑s : set α) :=
finset.subtype.fintype s

@[simp] lemma fintype.card_coe (s : finset α) :
  fintype.card (↑s : set α) = s.card := card_attach

lemma finset.attach_eq_univ {s : finset α} : s.attach = finset.univ := rfl

lemma finset.card_le_one_iff {s : finset α} :
  s.card ≤ 1 ↔ ∀ {x y}, x ∈ s → y ∈ s → x = y :=
begin
  let t : set α := ↑s,
  letI : fintype t := finset_coe.fintype s,
  have : fintype.card t = s.card := fintype.card_coe s,
  rw [← this, fintype.card_le_one_iff],
  split,
  { assume H x y hx hy,
    exact subtype.mk.inj (H ⟨x, hx⟩ ⟨y, hy⟩) },
  { assume H x y,
    exact subtype.eq (H x.2 y.2) }
end

/-- A `finset` of a subsingleton type has cardinality at most one. -/
lemma finset.card_le_one_of_subsingleton [subsingleton α] (s : finset α) : s.card ≤ 1 :=
finset.card_le_one_iff.2 $ λ _ _ _ _, subsingleton.elim _ _

lemma finset.one_lt_card_iff {s : finset α} :
  1 < s.card ↔ ∃ x y, (x ∈ s) ∧ (y ∈ s) ∧ x ≠ y :=
begin
  classical,
  rw ← not_iff_not,
  push_neg,
  simpa [or_iff_not_imp_left] using finset.card_le_one_iff
end

instance plift.fintype (p : Prop) [decidable p] : fintype (plift p) :=
⟨if h : p then {⟨h⟩} else ∅, λ ⟨h⟩, by simp [h]⟩

instance Prop.fintype : fintype Prop :=
⟨⟨true ::ₘ false ::ₘ 0, by simp [true_ne_false]⟩,
 classical.cases (by simp) (by simp)⟩

instance subtype.fintype (p : α → Prop) [decidable_pred p] [fintype α] : fintype {x // p x} :=
fintype.subtype (univ.filter p) (by simp)

/-- A set on a fintype, when coerced to a type, is a fintype. -/
def set_fintype {α} [fintype α] (s : set α) [decidable_pred s] : fintype s :=
subtype.fintype (λ x, x ∈ s)

namespace function.embedding

/-- An embedding from a `fintype` to itself can be promoted to an equivalence. -/
noncomputable def equiv_of_fintype_self_embedding {α : Type*} [fintype α] (e : α ↪ α) : α ≃ α :=
equiv.of_bijective e (fintype.injective_iff_bijective.1 e.2)

@[simp]
lemma equiv_of_fintype_self_embedding_to_embedding {α : Type*} [fintype α] (e : α ↪ α) :
  e.equiv_of_fintype_self_embedding.to_embedding = e :=
by { ext, refl, }

end function.embedding

@[simp]
lemma finset.univ_map_embedding {α : Type*} [fintype α] (e : α ↪ α) :
  univ.map e = univ :=
by rw [← e.equiv_of_fintype_self_embedding_to_embedding, univ_map_equiv_to_embedding]

namespace fintype

variables [decidable_eq α] [fintype α] {δ : α → Type*}

/-- Given for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `fintype.pi_finset t` of all functions taking values in `t a` for all `a`. This is the
analogue of `finset.pi` where the base finset is `univ` (but formally they are not the same, as
there is an additional condition `i ∈ finset.univ` in the `finset.pi` definition). -/
def pi_finset (t : Πa, finset (δ a)) : finset (Πa, δ a) :=
(finset.univ.pi t).map ⟨λ f a, f a (mem_univ a), λ _ _, by simp [function.funext_iff]⟩

@[simp] lemma mem_pi_finset {t : Πa, finset (δ a)} {f : Πa, δ a} :
  f ∈ pi_finset t ↔ (∀a, f a ∈ t a) :=
begin
  split,
  { simp only [pi_finset, mem_map, and_imp, forall_prop_of_true, exists_prop, mem_univ,
               exists_imp_distrib, mem_pi],
    assume g hg hgf a,
    rw ← hgf,
    exact hg a },
  { simp only [pi_finset, mem_map, forall_prop_of_true, exists_prop, mem_univ, mem_pi],
    assume hf,
    exact ⟨λ a ha, f a, hf, rfl⟩ }
end

lemma pi_finset_subset (t₁ t₂ : Πa, finset (δ a)) (h : ∀ a, t₁ a ⊆ t₂ a) :
  pi_finset t₁ ⊆ pi_finset t₂ :=
λ g hg, mem_pi_finset.2 $ λ a, h a $ mem_pi_finset.1 hg a

lemma pi_finset_disjoint_of_disjoint [∀ a, decidable_eq (δ a)]
  (t₁ t₂ : Πa, finset (δ a)) {a : α} (h : disjoint (t₁ a) (t₂ a)) :
  disjoint (pi_finset t₁) (pi_finset t₂) :=
disjoint_iff_ne.2 $ λ f₁ hf₁ f₂ hf₂ eq₁₂,
disjoint_iff_ne.1 h (f₁ a) (mem_pi_finset.1 hf₁ a) (f₂ a) (mem_pi_finset.1 hf₂ a) (congr_fun eq₁₂ a)

end fintype

/-! ### pi -/

/-- A dependent product of fintypes, indexed by a fintype, is a fintype. -/
instance pi.fintype {α : Type*} {β : α → Type*}
  [decidable_eq α] [fintype α] [∀a, fintype (β a)] : fintype (Πa, β a) :=
⟨fintype.pi_finset (λ _, univ), by simp⟩

@[simp] lemma fintype.pi_finset_univ {α : Type*} {β : α → Type*}
  [decidable_eq α] [fintype α] [∀a, fintype (β a)] :
  fintype.pi_finset (λ a : α, (finset.univ : finset (β a))) = (finset.univ : finset (Π a, β a)) :=
rfl

instance d_array.fintype {n : ℕ} {α : fin n → Type*}
  [∀n, fintype (α n)] : fintype (d_array n α) :=
fintype.of_equiv _ (equiv.d_array_equiv_fin _).symm

instance array.fintype {n : ℕ} {α : Type*} [fintype α] : fintype (array n α) :=
d_array.fintype

instance vector.fintype {α : Type*} [fintype α] {n : ℕ} : fintype (vector α n) :=
fintype.of_equiv _ (equiv.vector_equiv_fin _ _).symm

instance quotient.fintype [fintype α] (s : setoid α)
  [decidable_rel ((≈) : α → α → Prop)] : fintype (quotient s) :=
fintype.of_surjective quotient.mk (λ x, quotient.induction_on x (λ x, ⟨x, rfl⟩))

instance finset.fintype [fintype α] : fintype (finset α) :=
⟨univ.powerset, λ x, finset.mem_powerset.2 (finset.subset_univ _)⟩

@[simp] lemma fintype.card_finset [fintype α] :
  fintype.card (finset α) = 2 ^ (fintype.card α) :=
finset.card_powerset finset.univ

@[simp] lemma set.to_finset_univ [fintype α] :
  (set.univ : set α).to_finset = finset.univ :=
by { ext, simp only [set.mem_univ, mem_univ, set.mem_to_finset] }

@[simp] lemma set.to_finset_empty [fintype α] :
  (∅ : set α).to_finset = ∅ :=
by { ext, simp only [set.mem_empty_eq, set.mem_to_finset, not_mem_empty] }

theorem fintype.card_subtype_le [fintype α] (p : α → Prop) [decidable_pred p] :
  fintype.card {x // p x} ≤ fintype.card α :=
fintype.card_le_of_embedding (function.embedding.subtype _)

theorem fintype.card_subtype_lt [fintype α] {p : α → Prop} [decidable_pred p]
  {x : α} (hx : ¬ p x) : fintype.card {x // p x} < fintype.card α :=
fintype.card_lt_of_injective_of_not_mem coe subtype.coe_injective $ by rwa subtype.range_coe_subtype

instance psigma.fintype {α : Type*} {β : α → Type*} [fintype α] [∀ a, fintype (β a)] :
  fintype (Σ' a, β a) :=
fintype.of_equiv _ (equiv.psigma_equiv_sigma _).symm

instance psigma.fintype_prop_left {α : Prop} {β : α → Type*} [decidable α] [∀ a, fintype (β a)] :
  fintype (Σ' a, β a) :=
if h : α then fintype.of_equiv (β h) ⟨λ x, ⟨h, x⟩, psigma.snd, λ _, rfl, λ ⟨_, _⟩, rfl⟩
else ⟨∅, λ x, h x.1⟩

instance psigma.fintype_prop_right {α : Type*} {β : α → Prop} [∀ a, decidable (β a)] [fintype α] :
  fintype (Σ' a, β a) :=
fintype.of_equiv {a // β a} ⟨λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨x, y⟩, rfl, λ ⟨x, y⟩, rfl⟩

instance psigma.fintype_prop_prop {α : Prop} {β : α → Prop} [decidable α] [∀ a, decidable (β a)] :
  fintype (Σ' a, β a) :=
if h : ∃ a, β a then ⟨{⟨h.fst, h.snd⟩}, λ ⟨_, _⟩, by simp⟩ else ⟨∅, λ ⟨x, y⟩, h ⟨x, y⟩⟩

instance set.fintype [fintype α] : fintype (set α) :=
⟨(@finset.univ α _).powerset.map ⟨coe, coe_injective⟩, λ s, begin
  classical, refine mem_map.2 ⟨finset.univ.filter s, mem_powerset.2 (subset_univ _), _⟩,
  apply (coe_filter _ _).trans, rw [coe_univ, set.sep_univ], refl
end⟩

instance pfun_fintype (p : Prop) [decidable p] (α : p → Type*)
  [Π hp, fintype (α hp)] : fintype (Π hp : p, α hp) :=
if hp : p then fintype.of_equiv (α hp) ⟨λ a _, a, λ f, f hp, λ _, rfl, λ _, rfl⟩
          else ⟨singleton (λ h, (hp h).elim), by simp [hp, function.funext_iff]⟩

@[simp] lemma finset.univ_pi_univ {α : Type*} {β : α → Type*}
  [decidable_eq α] [fintype α] [∀a, fintype (β a)] :
  finset.univ.pi (λ a : α, (finset.univ : finset (β a))) = finset.univ :=
by { ext, simp }

lemma mem_image_univ_iff_mem_range
  {α β : Type*} [fintype α] [decidable_eq β] {f : α → β} {b : β} :
  b ∈ univ.image f ↔ b ∈ set.range f :=
by simp

/-- An auxiliary function for `quotient.fin_choice`.  Given a
collection of setoids indexed by a type `ι`, a (finite) list `l` of
indices, and a function that for each `i ∈ l` gives a term of the
corresponding quotient type, then there is a corresponding term in the
quotient of the product of the setoids indexed by `l`. -/
def quotient.fin_choice_aux {ι : Type*} [decidable_eq ι]
  {α : ι → Type*} [S : ∀ i, setoid (α i)] :
  Π (l : list ι), (Π i ∈ l, quotient (S i)) → @quotient (Π i ∈ l, α i) (by apply_instance)
| []     f := ⟦λ i, false.elim⟧
| (i::l) f := begin
  refine quotient.lift_on₂ (f i (list.mem_cons_self _ _))
    (quotient.fin_choice_aux l (λ j h, f j (list.mem_cons_of_mem _ h)))
    _ _,
  exact λ a l, ⟦λ j h,
    if e : j = i then by rw e; exact a else
    l _ (h.resolve_left e)⟧,
  refine λ a₁ l₁ a₂ l₂ h₁ h₂, quotient.sound (λ j h, _),
  by_cases e : j = i; simp [e],
  { subst j, exact h₁ },
  { exact h₂ _ _ }
end

theorem quotient.fin_choice_aux_eq {ι : Type*} [decidable_eq ι]
  {α : ι → Type*} [S : ∀ i, setoid (α i)] :
  ∀ (l : list ι) (f : Π i ∈ l, α i), quotient.fin_choice_aux l (λ i h, ⟦f i h⟧) = ⟦f⟧
| []     f := quotient.sound (λ i h, h.elim)
| (i::l) f := begin
  simp [quotient.fin_choice_aux, quotient.fin_choice_aux_eq l],
  refine quotient.sound (λ j h, _),
  by_cases e : j = i; simp [e],
  subst j, refl
end

/-- Given a collection of setoids indexed by a fintype `ι` and a
function that for each `i : ι` gives a term of the corresponding
quotient type, then there is corresponding term in the quotient of the
product of the setoids. -/
def quotient.fin_choice {ι : Type*} [decidable_eq ι] [fintype ι]
  {α : ι → Type*} [S : ∀ i, setoid (α i)]
  (f : Π i, quotient (S i)) : @quotient (Π i, α i) (by apply_instance) :=
quotient.lift_on (@quotient.rec_on _ _ (λ l : multiset ι,
    @quotient (Π i ∈ l, α i) (by apply_instance))
    finset.univ.1
    (λ l, quotient.fin_choice_aux l (λ i _, f i))
    (λ a b h, begin
      have := λ a, quotient.fin_choice_aux_eq a (λ i h, quotient.out (f i)),
      simp [quotient.out_eq] at this,
      simp [this],
      let g := λ a:multiset ι, ⟦λ (i : ι) (h : i ∈ a), quotient.out (f i)⟧,
      refine eq_of_heq ((eq_rec_heq _ _).trans (_ : g a == g b)),
      congr' 1, exact quotient.sound h,
    end))
  (λ f, ⟦λ i, f i (finset.mem_univ _)⟧)
  (λ a b h, quotient.sound $ λ i, h _ _)

theorem quotient.fin_choice_eq {ι : Type*} [decidable_eq ι] [fintype ι]
  {α : ι → Type*} [∀ i, setoid (α i)]
  (f : Π i, α i) : quotient.fin_choice (λ i, ⟦f i⟧) = ⟦f⟧ :=
begin
  let q, swap, change quotient.lift_on q _ _ = _,
  have : q = ⟦λ i h, f i⟧,
  { dsimp [q],
    exact quotient.induction_on
      (@finset.univ ι _).1 (λ l, quotient.fin_choice_aux_eq _ _) },
  simp [this], exact setoid.refl _
end

section equiv

open list equiv equiv.perm

variables [decidable_eq α] [decidable_eq β]

/-- Given a list, produce a list of all permutations of its elements. -/
def perms_of_list : list α → list (perm α)
| []       := [1]
| (a :: l) := perms_of_list l ++ l.bind (λ b, (perms_of_list l).map (λ f, swap a b * f))

lemma length_perms_of_list : ∀ l : list α, length (perms_of_list l) = l.length!
| []       := rfl
| (a :: l) :=
begin
  rw [length_cons, nat.factorial_succ],
  simp [perms_of_list, length_bind, length_perms_of_list, function.comp, nat.succ_mul],
  cc
end

lemma mem_perms_of_list_of_mem {l : list α} {f : perm α}
  (h : ∀ x, f x ≠ x → x ∈ l) : f ∈ perms_of_list l :=
begin
  induction l with a l IH generalizing f h,
  { exact list.mem_singleton.2 (equiv.ext $ λ x, decidable.by_contradiction $ h _) },
  by_cases hfa : f a = a,
  { refine mem_append_left _ (IH (λ x hx, mem_of_ne_of_mem _ (h x hx))),
    rintro rfl, exact hx hfa },
  { have hfa' : f (f a) ≠ f a := mt (λ h, f.injective h) hfa,
    have : ∀ (x : α), (swap a (f a) * f) x ≠ x → x ∈ l,
    { intros x hx,
      have hxa : x ≠ a,
      { rintro rfl, apply hx, simp only [mul_apply, swap_apply_right] },
      refine list.mem_of_ne_of_mem hxa (h x (λ h, _)),
      simp only [h, mul_apply, swap_apply_def, mul_apply, ne.def, apply_eq_iff_eq] at hx;
      split_ifs at hx, exacts [hxa (h.symm.trans h_1), hx h] },
    suffices : f ∈ perms_of_list l ∨ ∃ (b ∈ l) (g ∈ perms_of_list l), swap a b * g = f,
    { simpa only [perms_of_list, exists_prop, list.mem_map, mem_append, list.mem_bind] },
    refine or_iff_not_imp_left.2 (λ hfl, ⟨f a, _, swap a (f a) * f, IH this, _⟩),
    { by_cases hffa : f (f a) = a,
      { exact mem_of_ne_of_mem hfa (h _ (mt (λ h, f.injective h) hfa)) },
      { apply this,
        simp only [mul_apply, swap_apply_def, mul_apply, ne.def, apply_eq_iff_eq],
        split_ifs; cc } },
    { rw [← mul_assoc, mul_def (swap a (f a)) (swap a (f a)),
          swap_swap, ← equiv.perm.one_def, one_mul] } }
end

lemma mem_of_mem_perms_of_list :
  ∀ {l : list α} {f : perm α}, f ∈ perms_of_list l → ∀ {x}, f x ≠ x → x ∈ l
| []     f h := have f = 1 := by simpa [perms_of_list] using h, by rw this; simp
| (a::l) f h :=
(mem_append.1 h).elim
  (λ h x hx, mem_cons_of_mem _ (mem_of_mem_perms_of_list h hx))
  (λ h x hx,
    let ⟨y, hy, hy'⟩ := list.mem_bind.1 h in
    let ⟨g, hg₁, hg₂⟩ := list.mem_map.1 hy' in
    if hxa : x = a then by simp [hxa]
    else if hxy : x = y then mem_cons_of_mem _ $ by rwa hxy
    else mem_cons_of_mem _ $
    mem_of_mem_perms_of_list hg₁ $
      by rw [eq_inv_mul_iff_mul_eq.2 hg₂, mul_apply, swap_inv, swap_apply_def];
        split_ifs; cc)

lemma mem_perms_of_list_iff {l : list α} {f : perm α} :
  f ∈ perms_of_list l ↔ ∀ {x}, f x ≠ x → x ∈ l :=
⟨mem_of_mem_perms_of_list, mem_perms_of_list_of_mem⟩

lemma nodup_perms_of_list : ∀ {l : list α} (hl : l.nodup), (perms_of_list l).nodup
| []     hl := by simp [perms_of_list]
| (a::l) hl :=
have hl' : l.nodup, from nodup_of_nodup_cons hl,
have hln' : (perms_of_list l).nodup, from nodup_perms_of_list hl',
have hmeml : ∀ {f : perm α}, f ∈ perms_of_list l → f a = a,
  from λ f hf, not_not.1 (mt (mem_of_mem_perms_of_list hf) (nodup_cons.1 hl).1),
by rw [perms_of_list, list.nodup_append, list.nodup_bind, pairwise_iff_nth_le]; exact
⟨hln', ⟨λ _ _, nodup_map (λ _ _, mul_left_cancel) hln',
  λ i j hj hij x hx₁ hx₂,
    let ⟨f, hf⟩ := list.mem_map.1 hx₁ in
    let ⟨g, hg⟩ := list.mem_map.1 hx₂ in
    have hix : x a = nth_le l i (lt_trans hij hj),
      by rw [← hf.2, mul_apply, hmeml hf.1, swap_apply_left],
    have hiy : x a = nth_le l j hj,
      by rw [← hg.2, mul_apply, hmeml hg.1, swap_apply_left],
    absurd (hf.2.trans (hg.2.symm)) $
      λ h, ne_of_lt hij $ nodup_iff_nth_le_inj.1 hl' i j (lt_trans hij hj) hj $
        by rw [← hix, hiy]⟩,
  λ f hf₁ hf₂,
    let ⟨x, hx, hx'⟩ := list.mem_bind.1 hf₂ in
    let ⟨g, hg⟩ := list.mem_map.1 hx' in
    have hgxa : g⁻¹ x = a, from f.injective $
      by rw [hmeml hf₁, ← hg.2]; simp,
    have hxa : x ≠ a, from λ h, (list.nodup_cons.1 hl).1 (h ▸ hx),
    (list.nodup_cons.1 hl).1 $
      hgxa ▸ mem_of_mem_perms_of_list hg.1 (by rwa [apply_inv_self, hgxa])⟩

/-- Given a finset, produce the finset of all permutations of its elements. -/
def perms_of_finset (s : finset α) : finset (perm α) :=
quotient.hrec_on s.1 (λ l hl, ⟨perms_of_list l, nodup_perms_of_list hl⟩)
  (λ a b hab, hfunext (congr_arg _ (quotient.sound hab))
    (λ ha hb _, heq_of_eq $ finset.ext $
      by simp [mem_perms_of_list_iff, hab.mem_iff]))
  s.2

lemma mem_perms_of_finset_iff : ∀ {s : finset α} {f : perm α},
  f ∈ perms_of_finset s ↔ ∀ {x}, f x ≠ x → x ∈ s :=
by rintros ⟨⟨l⟩, hs⟩ f; exact mem_perms_of_list_iff

lemma card_perms_of_finset : ∀ (s : finset α),
  (perms_of_finset s).card = s.card! :=
by rintros ⟨⟨l⟩, hs⟩; exact length_perms_of_list l

/-- The collection of permutations of a fintype is a fintype. -/
def fintype_perm [fintype α] : fintype (perm α) :=
⟨perms_of_finset (@finset.univ α _), by simp [mem_perms_of_finset_iff]⟩

instance [fintype α] [fintype β] : fintype (α ≃ β) :=
if h : fintype.card β = fintype.card α
then trunc.rec_on_subsingleton (fintype.equiv_fin α)
  (λ eα, trunc.rec_on_subsingleton (fintype.equiv_fin β)
    (λ eβ, @fintype.of_equiv _ (perm α) fintype_perm
      (equiv_congr (equiv.refl α) (eα.trans (eq.rec_on h eβ.symm)) : (α ≃ α) ≃ (α ≃ β))))
else ⟨∅, λ x, false.elim (h (fintype.card_eq.2 ⟨x.symm⟩))⟩

lemma fintype.card_perm [fintype α] : fintype.card (perm α) = (fintype.card α)! :=
subsingleton.elim (@fintype_perm α _ _) (@equiv.fintype α α _ _ _ _) ▸
card_perms_of_finset _

lemma fintype.card_equiv [fintype α] [fintype β] (e : α ≃ β) :
  fintype.card (α ≃ β) = (fintype.card α)! :=
fintype.card_congr (equiv_congr (equiv.refl α) e) ▸ fintype.card_perm

lemma univ_eq_singleton_of_card_one {α} [fintype α] (x : α) (h : fintype.card α = 1) :
  (univ : finset α) = {x} :=
begin
  symmetry,
  apply eq_of_subset_of_card_le (subset_univ ({x})),
  apply le_of_eq,
  simp [h, finset.card_univ]
end

end equiv

namespace fintype

section choose
open fintype
open equiv

variables [fintype α] (p : α → Prop) [decidable_pred p]

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def choose_x (hp : ∃! a : α, p a) : {a // p a} :=
⟨finset.choose p univ (by simp; exact hp), finset.choose_property _ _ _⟩

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of `α`. -/
def choose (hp : ∃! a, p a) : α := choose_x p hp

lemma choose_spec (hp : ∃! a, p a) : p (choose p hp) :=
(choose_x p hp).property

end choose

section bijection_inverse
open function

variables [fintype α]
variables [decidable_eq β]
variables {f : α → β}

/-- `
`bij_inv f` is the unique inverse to a bijection `f`. This acts
  as a computable alternative to `function.inv_fun`. -/
def bij_inv (f_bij : bijective f) (b : β) : α :=
fintype.choose (λ a, f a = b)
begin
  rcases f_bij.right b with ⟨a', fa_eq_b⟩,
  rw ← fa_eq_b,
  exact ⟨a', ⟨rfl, (λ a h, f_bij.left h)⟩⟩
end

lemma left_inverse_bij_inv (f_bij : bijective f) : left_inverse (bij_inv f_bij) f :=
λ a, f_bij.left (choose_spec (λ a', f a' = f a) _)

lemma right_inverse_bij_inv (f_bij : bijective f) : right_inverse (bij_inv f_bij) f :=
λ b, choose_spec (λ a', f a' = b) _

lemma bijective_bij_inv (f_bij : bijective f) : bijective (bij_inv f_bij) :=
⟨(right_inverse_bij_inv _).injective, (left_inverse_bij_inv _).surjective⟩

end bijection_inverse

lemma well_founded_of_trans_of_irrefl [fintype α] (r : α → α → Prop)
  [is_trans α r] [is_irrefl α r] : well_founded r :=
by classical; exact
have ∀ x y, r x y → (univ.filter (λ z, r z x)).card < (univ.filter (λ z, r z y)).card,
  from λ x y hxy, finset.card_lt_card $
    by simp only [finset.lt_iff_ssubset.symm, lt_iff_le_not_le,
      finset.le_iff_subset, finset.subset_iff, mem_filter, true_and, mem_univ, hxy];
    exact ⟨λ z hzx, trans hzx hxy, not_forall_of_exists_not ⟨x, not_imp.2 ⟨hxy, irrefl x⟩⟩⟩,
subrelation.wf this (measure_wf _)

lemma preorder.well_founded [fintype α] [preorder α] : well_founded ((<) : α → α → Prop) :=
well_founded_of_trans_of_irrefl _

@[instance, priority 10] lemma linear_order.is_well_order [fintype α] [linear_order α] :
  is_well_order α (<) :=
{ wf := preorder.well_founded }

end fintype

/-- A type is said to be infinite if it has no fintype instance. -/
class infinite (α : Type*) : Prop :=
(not_fintype : fintype α → false)

@[simp] lemma not_nonempty_fintype {α : Type*} : ¬nonempty (fintype α) ↔ infinite α :=
⟨λf, ⟨λ x, f ⟨x⟩⟩, λ⟨f⟩ ⟨x⟩, f x⟩

lemma finset.exists_minimal {α : Type*} [preorder α] (s : finset α) (h : s.nonempty) :
  ∃ m ∈ s, ∀ x ∈ s, ¬ (x < m) :=
begin
  obtain ⟨c, hcs : c ∈ s⟩ := h,
  have : well_founded (@has_lt.lt {x // x ∈ s} _) := fintype.well_founded_of_trans_of_irrefl _,
  obtain ⟨⟨m, hms : m ∈ s⟩, -, H⟩ := this.has_min set.univ ⟨⟨c, hcs⟩, trivial⟩,
  exact ⟨m, hms, λ x hx hxm, H ⟨x, hx⟩ trivial hxm⟩,
end

lemma finset.exists_maximal {α : Type*} [preorder α] (s : finset α) (h : s.nonempty) :
  ∃ m ∈ s, ∀ x ∈ s, ¬ (m < x) :=
@finset.exists_minimal (order_dual α) _ s h

namespace infinite

lemma exists_not_mem_finset [infinite α] (s : finset α) : ∃ x, x ∉ s :=
not_forall.1 $ λ h, not_fintype ⟨s, h⟩

@[priority 100] -- see Note [lower instance priority]
instance (α : Type*) [H : infinite α] : nontrivial α :=
⟨let ⟨x, hx⟩ := exists_not_mem_finset (∅ : finset α) in
let ⟨y, hy⟩ := exists_not_mem_finset ({x} : finset α) in
⟨y, x, by simpa only [mem_singleton] using hy⟩⟩

lemma nonempty (α : Type*) [infinite α] : nonempty α :=
by apply_instance

lemma of_injective [infinite β] (f : β → α) (hf : injective f) : infinite α :=
⟨λ I, by exactI not_fintype (fintype.of_injective f hf)⟩

lemma of_surjective [infinite β] (f : α → β) (hf : surjective f) : infinite α :=
⟨λ I, by classical; exactI not_fintype (fintype.of_surjective f hf)⟩

private noncomputable def nat_embedding_aux (α : Type*) [infinite α] : ℕ → α
| n := by letI := classical.dec_eq α; exact classical.some (exists_not_mem_finset
  ((multiset.range n).pmap (λ m (hm : m < n), nat_embedding_aux m)
    (λ _, multiset.mem_range.1)).to_finset)

private lemma nat_embedding_aux_injective (α : Type*) [infinite α] :
  function.injective (nat_embedding_aux α) :=
begin
  assume m n h,
  letI := classical.dec_eq α,
  wlog hmlen : m ≤ n using m n,
  by_contradiction hmn,
  have hmn : m < n, from lt_of_le_of_ne hmlen hmn,
  refine (classical.some_spec (exists_not_mem_finset
    ((multiset.range n).pmap (λ m (hm : m < n), nat_embedding_aux α m)
      (λ _, multiset.mem_range.1)).to_finset)) _,
  refine multiset.mem_to_finset.2 (multiset.mem_pmap.2
    ⟨m, multiset.mem_range.2 hmn, _⟩),
  rw [h, nat_embedding_aux]
end

/-- Embedding of `ℕ` into an infinite type. -/
noncomputable def nat_embedding (α : Type*) [infinite α] : ℕ ↪ α :=
⟨_, nat_embedding_aux_injective α⟩

lemma exists_subset_card_eq (α : Type*) [infinite α] (n : ℕ) :
  ∃ s : finset α, s.card = n :=
⟨(range n).map (nat_embedding α), by rw [card_map, card_range]⟩

end infinite

lemma not_injective_infinite_fintype [infinite α] [fintype β] (f : α → β) :
  ¬ injective f :=
assume (hf : injective f),
have H : fintype α := fintype.of_injective f hf,
infinite.not_fintype H

/--
The pigeonhole principle for infinitely many pigeons in finitely many
pigeonholes.  If there are infinitely many pigeons in finitely many
pigeonholes, then there are at least two pigeons in the same
pigeonhole.

See also: `fintype.exists_ne_map_eq_of_card_lt`, `fintype.exists_infinite_fiber`.
-/
lemma fintype.exists_ne_map_eq_of_infinite [infinite α] [fintype β] (f : α → β) :
  ∃ x y : α, x ≠ y ∧ f x = f y :=
begin
  classical, by_contra hf, push_neg at hf,
  apply not_injective_infinite_fintype f,
  intros x y, contrapose, apply hf,
end

/--
The strong pigeonhole principle for infinitely many pigeons in
finitely many pigeonholes.  If there are infinitely many pigeons in
finitely many pigeonholes, then there is a pigeonhole with infinitely
many pigeons.

See also: `fintype.exists_ne_map_eq_of_infinite`
-/
lemma fintype.exists_infinite_fiber [infinite α] [fintype β] (f : α → β) :
  ∃ y : β, infinite (f ⁻¹' {y}) :=
begin
  classical, by_contra hf, push_neg at hf,
  haveI h' : ∀ (y : β), fintype (f ⁻¹' {y}) := begin
    intro y, specialize hf y,
    rw [←not_nonempty_fintype, not_not] at hf,
    exact classical.choice hf,
  end,
  let key : fintype α :=
  { elems := univ.bUnion (λ (y : β), (f ⁻¹' {y}).to_finset),
    complete := by simp },
  exact infinite.not_fintype key,
end

lemma not_surjective_fintype_infinite [fintype α] [infinite β] (f : α → β) :
  ¬ surjective f :=
assume (hf : surjective f),
have H : infinite α := infinite.of_surjective f hf,
@infinite.not_fintype _ H infer_instance

instance nat.infinite : infinite ℕ :=
⟨λ ⟨s, hs⟩, finset.not_mem_range_self $ s.subset_range_sup_succ (hs _)⟩

instance int.infinite : infinite ℤ :=
infinite.of_injective int.of_nat (λ _ _, int.of_nat.inj)

section trunc

/--
For `s : multiset α`, we can lift the existential statement that `∃ x, x ∈ s` to a `trunc α`.
-/
def trunc_of_multiset_exists_mem {α} (s : multiset α) : (∃ x, x ∈ s) → trunc α :=
quotient.rec_on_subsingleton s $ λ l h,
  match l, h with
    | [],       _ := false.elim (by tauto)
    | (a :: _), _ := trunc.mk a
  end

/--
A `nonempty` `fintype` constructively contains an element.
-/
def trunc_of_nonempty_fintype (α) [nonempty α] [fintype α] : trunc α :=
trunc_of_multiset_exists_mem finset.univ.val (by simp)

/--
A `fintype` with positive cardinality constructively contains an element.
-/
def trunc_of_card_pos {α} [fintype α] (h : 0 < fintype.card α) : trunc α :=
by { letI := (fintype.card_pos_iff.mp h), exact trunc_of_nonempty_fintype α }

/--
By iterating over the elements of a fintype, we can lift an existential statement `∃ a, P a`
to `trunc (Σ' a, P a)`, containing data.
-/
def trunc_sigma_of_exists {α} [fintype α] {P : α → Prop} [decidable_pred P] (h : ∃ a, P a) :
  trunc (Σ' a, P a) :=
@trunc_of_nonempty_fintype (Σ' a, P a) (exists.elim h $ λ a ha, ⟨⟨a, ha⟩⟩) _

end trunc
