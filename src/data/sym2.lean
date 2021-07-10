/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import tactic.linarith
import data.sym

/-!
# The symmetric square

This file defines the symmetric square, which is `α × α` modulo
swapping.  This is also known as the type of unordered pairs.

More generally, the symmetric square is the second symmetric power
(see `data.sym`). The equivalence is `sym2.equiv_sym`.

From the point of view that an unordered pair is equivalent to a
multiset of cardinality two (see `sym2.equiv_multiset`), there is a
`has_mem` instance `sym2.mem`, which is a `Prop`-valued membership
test.  Given `h : a ∈ z` for `z : sym2 α`, then `h.other` is the other
element of the pair, defined using `classical.choice`.  If `α` has
decidable equality, then `h.other'` computably gives the other element.

Recall that an undirected graph (allowing self loops, but no multiple
edges) is equivalent to a symmetric relation on the vertex type `α`.
Given a symmetric relation on `α`, the corresponding edge set is
constructed by `sym2.from_rel`.

## Notation

The symmetric square has a setoid instance, so `⟦(a, b)⟧` denotes a
term of the symmetric square.

## Tags

symmetric square, unordered pairs, symmetric powers
-/

open function
open sym

universe u
variables {α : Type u}
namespace sym2

/--
This is the relation capturing the notion of pairs equivalent up to permutations.
-/
inductive rel (α : Type u) : (α × α) → (α × α) → Prop
| refl (x y : α) : rel (x, y) (x, y)
| swap (x y : α) : rel (x, y) (y, x)

attribute [refl] rel.refl

@[symm] lemma rel.symm {x y : α × α} : rel α x y → rel α y x :=
by rintro ⟨_, _⟩; constructor

@[trans] lemma rel.trans {x y z : α × α} : rel α x y → rel α y z → rel α x z :=
by { intros a b, cases_matching* rel _ _ _; apply rel.refl <|> apply rel.swap }

lemma rel.is_equivalence : equivalence (rel α) := by tidy; apply rel.trans; assumption

instance rel.setoid (α : Type u) : setoid (α × α) := ⟨rel α, rel.is_equivalence⟩

end sym2

/--
`sym2 α` is the symmetric square of `α`, which, in other words, is the
type of unordered pairs.

It is equivalent in a natural way to multisets of cardinality 2 (see
`sym2.equiv_multiset`).
-/
@[reducible]
def sym2 (α : Type u) := quotient (sym2.rel.setoid α)

namespace sym2

lemma eq_swap {a b : α} : ⟦(a, b)⟧ = ⟦(b, a)⟧ :=
by { rw quotient.eq, apply rel.swap }

lemma congr_right {a b c : α} : ⟦(a, b)⟧ = ⟦(a, c)⟧ ↔ b = c :=
by { split; intro h, { rw quotient.eq at h, cases h; refl }, rw h }

lemma congr_left {a b c : α} : ⟦(b, a)⟧ = ⟦(c, a)⟧ ↔ b = c :=
by { split; intro h, { rw quotient.eq at h, cases h; refl }, rw h }

/--
The functor `sym2` is functorial, and this function constructs the induced maps.
-/
def map {α β : Type*} (f : α → β) : sym2 α → sym2 β :=
quotient.map (prod.map f f)
  (by { rintros _ _ h, cases h, { refl }, apply rel.swap })

@[simp]
lemma map_id : sym2.map (@id α) = id := by tidy

lemma map_comp {α β γ : Type*} {g : β → γ} {f : α → β} :
  sym2.map (g ∘ f) = sym2.map g ∘ sym2.map f := by tidy

@[simp]
lemma map_pair_eq {α β : Type*} (f : α → β) (x y : α) : map f ⟦(x, y)⟧ = ⟦(f x, f y)⟧ :=
by simp [map]

section membership

/-! ### Declarations about membership -/

/--
This is a predicate that determines whether a given term is a member of a term of the
symmetric square.  From this point of view, the symmetric square is the subtype of
cardinality-two multisets on `α`.
-/
def mem (x : α) (z : sym2 α) : Prop :=
∃ (y : α), z = ⟦(x, y)⟧

instance : has_mem α (sym2 α) := ⟨mem⟩

lemma mk_has_mem (x y : α) : x ∈ ⟦(x, y)⟧ := ⟨y, rfl⟩

lemma mk_has_mem_right (x y : α) : y ∈ ⟦(x, y)⟧ := by { rw eq_swap, apply mk_has_mem }

/--
Given an element of the unordered pair, give the other element using `classical.some`.
See also `mem.other'` for the computable version.
-/
noncomputable def mem.other {a : α} {z : sym2 α} (h : a ∈ z) : α :=
classical.some h

@[simp]
lemma mem_other_spec {a : α} {z : sym2 α} (h : a ∈ z) : ⟦(a, h.other)⟧ = z :=
by erw ← classical.some_spec h

lemma eq_iff {x y z w : α} :
  ⟦(x, y)⟧ = ⟦(z, w)⟧ ↔ (x = z ∧ y = w) ∨ (x = w ∧ y = z) :=
begin
  split; intro h,
  { rw quotient.eq at h, cases h; tidy },
  { cases h; rw [h.1, h.2], rw eq_swap }
end

@[simp] lemma mem_iff {a b c : α} : a ∈ ⟦(b, c)⟧ ↔ a = b ∨ a = c :=
{ mp  := by { rintro ⟨_, h⟩, rw eq_iff at h, tidy },
  mpr := by { rintro ⟨_⟩; subst a, { apply mk_has_mem }, apply mk_has_mem_right } }

lemma mem_other_mem {a : α} {z : sym2 α} (h : a ∈ z) :
  h.other ∈ z :=
by { convert mk_has_mem_right a h.other, rw mem_other_spec h }

lemma elems_iff_eq {x y : α} {z : sym2 α} (hne : x ≠ y) :
  x ∈ z ∧ y ∈ z ↔ z = ⟦(x, y)⟧ :=
begin
  split,
  { refine quotient.rec_on_subsingleton z _,
    rintros ⟨z₁, z₂⟩ ⟨hx, hy⟩,
    rw eq_iff,
    cases mem_iff.mp hx with hx hx; cases mem_iff.mp hy with hy hy; cc },
  { rintro rfl, simp },
end

@[ext]
lemma sym2_ext (z z' : sym2 α) (h : ∀ x, x ∈ z ↔ x ∈ z') : z = z' :=
begin
  refine quotient.rec_on_subsingleton z (λ w, _) h,
  refine quotient.rec_on_subsingleton z' (λ w', _),
  intro h,
  cases w with x y, cases w' with x' y',
  simp only [mem_iff] at h,
  apply eq_iff.mpr,
  have hx := h x, have hy := h y, have hx' := h x', have hy' := h y',
  simp only [true_iff, true_or, eq_self_iff_true, iff_true, or_true] at hx hy hx' hy',
  cases hx; subst x; cases hy; subst y; cases hx'; try { subst x' }; cases hy'; try { subst y' };
  cc,
end

instance mem.decidable [decidable_eq α] (x : α) (z : sym2 α) : decidable (x ∈ z) :=
quotient.rec_on_subsingleton z (λ ⟨y₁, y₂⟩, decidable_of_iff' _ mem_iff)

end membership

/--
A type `α` is naturally included in the diagonal of `α × α`, and this function gives the image
of this diagonal in `sym2 α`.
-/
def diag (x : α) : sym2 α := ⟦(x, x)⟧

/--
A predicate for testing whether an element of `sym2 α` is on the diagonal.
-/
def is_diag (z : sym2 α) : Prop := z ∈ set.range (@diag α)

@[simp]
lemma diag_is_diag (a : α) : is_diag (diag a) :=
by use a

@[simp]
lemma is_diag_iff_proj_eq (z : α × α) : is_diag ⟦z⟧ ↔ z.1 = z.2 :=
begin
  cases z with a, split,
  { rintro ⟨_, h⟩, dsimp only, erw eq_iff at h, rcases h; cc },
  { rintro ⟨⟩, use a, refl },
end

instance is_diag.decidable_pred (α : Type u) [decidable_eq α] : decidable_pred (@is_diag α) :=
by { refine λ z, quotient.rec_on_subsingleton z (λ a, _), erw is_diag_iff_proj_eq, apply_instance }

lemma mem_other_ne {a : α} {z : sym2 α} (hd : ¬is_diag z) (h : a ∈ z) : h.other ≠ a :=
begin
  intro hn, apply hd,
  have h' := sym2.mem_other_spec h,
  rw hn at h',
  rw ←h',
  simp,
end

section relations

/-! ### Declarations about symmetric relations -/

variables {r : α → α → Prop}

/--
Symmetric relations define a set on `sym2 α` by taking all those pairs
of elements that are related.
-/
def from_rel (sym : symmetric r) : set (sym2 α) :=
quotient.lift (uncurry r) (by { rintros _ _ ⟨_, _⟩, tidy })

@[simp]
lemma from_rel_proj_prop {sym : symmetric r} {z : α × α} :
  ⟦z⟧ ∈ from_rel sym ↔ r z.1 z.2 := iff.rfl

@[simp]
lemma from_rel_prop {sym : symmetric r} {a b : α} :
  ⟦(a, b)⟧ ∈ from_rel sym ↔ r a b := by simp only [from_rel_proj_prop]

lemma from_rel_irreflexive {sym : symmetric r} :
  irreflexive r ↔ ∀ {z}, z ∈ from_rel sym → ¬is_diag z :=
{ mp  := by { intros h z hr hd, induction z,
              erw is_diag_iff_proj_eq at hd, erw from_rel_proj_prop at hr, tidy },
  mpr := by { intros h x hr, rw ← @from_rel_prop _ _ sym at hr, exact h hr ⟨x, rfl⟩ }}

lemma mem_from_rel_irrefl_other_ne {sym : symmetric r} (irrefl : irreflexive r)
  {a : α} {z : sym2 α} (hz : z ∈ from_rel sym) (h : a ∈ z) : h.other ≠ a :=
mem_other_ne (from_rel_irreflexive.mp irrefl hz) h

instance from_rel.decidable_pred (sym : symmetric r) [h : decidable_rel r] :
  decidable_pred (∈ sym2.from_rel sym) :=
λ z, quotient.rec_on_subsingleton z (λ x, h _ _)

end relations

section sym_equiv

/-! ### Equivalence to the second symmetric power -/

local attribute [instance] vector.perm.is_setoid

private def from_vector {α : Type*} : vector α 2 → α × α
| ⟨[a, b], h⟩ := (a, b)

private lemma perm_card_two_iff {α : Type*} {a₁ b₁ a₂ b₂ : α} :
  [a₁, b₁].perm [a₂, b₂] ↔ (a₁ = a₂ ∧ b₁ = b₂) ∨ (a₁ = b₂ ∧ b₁ = a₂) :=
{ mp  := by { simp [← multiset.coe_eq_coe, ← multiset.cons_coe, multiset.cons_eq_cons]; tidy },
  mpr := by { intro h, cases h; rw [h.1, h.2], apply list.perm.swap', refl } }

/--
The symmetric square is equivalent to length-2 vectors up to permutations.
-/
def sym2_equiv_sym' {α : Type*} : equiv (sym2 α) (sym' α 2) :=
{ to_fun := quotient.map
    (λ (x : α × α), ⟨[x.1, x.2], rfl⟩)
    (by { rintros _ _ ⟨_⟩, { refl }, apply list.perm.swap', refl }),
  inv_fun := quotient.map from_vector (begin
    rintros ⟨x, hx⟩ ⟨y, hy⟩ h,
    cases x with _ x, { simpa using hx, },
    cases x with _ x, { simpa using hx, },
    cases x with _ x, swap, { exfalso, simp at hx, linarith [hx] },
    cases y with _ y, { simpa using hy, },
    cases y with _ y, { simpa using hy, },
    cases y with _ y, swap, { exfalso, simp at hy, linarith [hy] },
    rcases perm_card_two_iff.mp h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩, { refl },
    apply sym2.rel.swap,
  end),
  left_inv := by tidy,
  right_inv := λ x, begin
    refine quotient.rec_on_subsingleton x (λ x, _),
    { cases x with x hx,
      cases x with _ x, { simpa using hx, },
      cases x with _ x, { simpa using hx, },
      cases x with _ x, swap, { exfalso, simp at hx, linarith [hx] },
      refl },
  end }

/--
The symmetric square is equivalent to the second symmetric power.
-/
def equiv_sym (α : Type*) : sym2 α ≃ sym α 2 :=
equiv.trans sym2_equiv_sym' sym_equiv_sym'.symm

/--
The symmetric square is equivalent to multisets of cardinality
two. (This is currently a synonym for `equiv_sym`, but it's provided
in case the definition for `sym` changes.)
-/
def equiv_multiset (α : Type*) : sym2 α ≃ {s : multiset α // s.card = 2} :=
equiv_sym α

end sym_equiv

section decidable

/--
An algorithm for computing `sym2.rel`.
-/
def rel_bool [decidable_eq α] (x y : α × α) : bool :=
if x.1 = y.1 then x.2 = y.2 else
  if x.1 = y.2 then x.2 = y.1 else ff

lemma rel_bool_spec [decidable_eq α] (x y : α × α) :
  ↥(rel_bool x y) ↔ rel α x y :=
begin
  cases x with x₁ x₂, cases y with y₁ y₂,
  dsimp [rel_bool], split_ifs;
  simp only [false_iff, bool.coe_sort_ff, bool.of_to_bool_iff],
  rotate 2, { contrapose! h, cases h; cc },
  all_goals { subst x₁, split; intro h1,
    { subst h1; apply sym2.rel.swap },
    { cases h1; cc } }
end

/--
Given `[decidable_eq α]` and `[fintype α]`, the following instance gives `fintype (sym2 α)`.
-/
instance (α : Type*) [decidable_eq α] : decidable_rel (sym2.rel α) :=
λ x y, decidable_of_bool (rel_bool x y) (rel_bool_spec x y)

/--
A function that gives the other element of a pair given one of the elements.  Used in `mem.other'`.
-/
private def pair_other [decidable_eq α] (a : α) (z : α × α) : α := if a = z.1 then z.2 else z.1

/--
Get the other element of the unordered pair using the decidable equality.
This is the computable version of `mem.other`.
-/
def mem.other' [decidable_eq α] {a : α} {z : sym2 α} (h : a ∈ z) : α :=
quot.rec (λ x h', pair_other a x) (begin
  clear h z,
  intros x y h,
  ext hy,
  convert_to pair_other a x = _,
  { have h' : ∀ {c e h}, @eq.rec _ ⟦x⟧ (λ s, a ∈ s → α)
      (λ _, pair_other a x) c e h = pair_other a x,
    { intros _ e _, subst e },
    apply h', },
  have h' := (rel_bool_spec x y).mpr h,
  cases x with x₁ x₂, cases y with y₁ y₂,
  cases mem_iff.mp hy with hy'; subst a; dsimp [rel_bool] at h';
    split_ifs at h'; try { rw bool.of_to_bool_iff at h', subst x₁, subst x₂ }; dsimp [pair_other],
  simp only [ne.symm h_1, if_true, eq_self_iff_true, if_false],
  exfalso, exact bool.not_ff h',
  simp only [h_1, if_true, eq_self_iff_true, if_false],
  exfalso, exact bool.not_ff h',
end) z h

@[simp]
lemma mem_other_spec' [decidable_eq α] {a : α} {z : sym2 α} (h : a ∈ z) :
  ⟦(a, h.other')⟧ = z :=
begin
  induction z, cases z with x y,
  have h' := mem_iff.mp h,
  dsimp [mem.other', quot.rec, pair_other],
  cases h'; subst a,
  { simp only [if_true, eq_self_iff_true], refl, },
  { split_ifs, subst h_1, refl, rw eq_swap, refl, },
  refl,
end

@[simp]
lemma other_eq_other' [decidable_eq α] {a : α} {z : sym2 α} (h : a ∈ z) : h.other = h.other' :=
by rw [←congr_right, mem_other_spec' h, mem_other_spec]

lemma mem_other_mem' [decidable_eq α] {a : α} {z : sym2 α} (h : a ∈ z) :
  h.other' ∈ z :=
by { rw ←other_eq_other', exact mem_other_mem h }

lemma other_invol' [decidable_eq α] {a : α} {z : sym2 α} (ha : a ∈ z) (hb : ha.other' ∈ z):
  hb.other' = a :=
begin
  induction z, cases z with x y,
  dsimp [mem.other', quot.rec, pair_other] at hb,
  split_ifs at hb; dsimp [mem.other', quot.rec, pair_other],
  simp only [h, if_true, eq_self_iff_true],
  split_ifs, assumption, refl,
  simp only [h, if_false, if_true, eq_self_iff_true],
  cases mem_iff.mp ha; cc,
  refl,
end

lemma other_invol {a : α} {z : sym2 α} (ha : a ∈ z) (hb : ha.other ∈ z):
  hb.other = a :=
begin
  classical,
  rw other_eq_other' at hb ⊢,
  convert other_invol' ha hb,
  rw other_eq_other',
end

end decidable

end sym2
