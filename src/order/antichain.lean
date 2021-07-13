/-
Copyright (c) 2020 Bhavik Mehta, Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/
import order.basic
import data.finset
import data.multiset.finset_ops

/-!
# Antichains
Investigating the structure of finsets in a partial order.
We define antichains.

## Main definitions
* `antichain` is a finset of elements in a partial order where
  no element is strictly less than another.

* The `join` of two finsets is the set obtained by taking
  their union and removing all elements that are less than
  another element.

* The `meet` of two finsets is their intersection.
-/

open partial_order

universe u

open_locale classical
noncomputable theory

variable {α : Type u}

section
variables [partial_order α]

/--
A set of elements of a partial order forms an antichain if no two elements
`A` and `B` are ordered `A < B`.
-/
def antichain (𝒜 : finset α) : Prop := ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, a ≤ b → a = b

lemma antichain_def (A : finset α) :
  antichain A ↔ ∀ a ∈ A, ∀ b ∈ A, a ≤ b → a = b := iff.rfl

theorem antichain.subset (A B : finset α) (ha : antichain A) (hb : B ⊆ A) :
  antichain B :=
begin
  intros a ha2 b hb2,
  apply ha a (finset.mem_of_subset hb ha2) b (finset.mem_of_subset hb hb2),
end

/--
The join of two finsets `A` and `B` is the set obtained by taking
the union of `A` and `B` and removing all elements `a` that are
less than some element `b`. This results in an antichain.
-/
def antichain.join (A B : finset α):
  finset α := (A ∪ B).filter (λ a, a ∈ A ∪ B ∧ ∀ b ∈ A ∪ B, a ≤ b → a = b)

/--
The meet of two finsets `A` and `B` is the set obtained by taking
the intersection of `A` and `B` and removing all elements `a` that are
less than some element `b`. This results in an antichain.
-/
def antichain.meet (A B : finset α) : finset α := A ∩ B

@[simp]
lemma antichain.mem_join_iff (A B : finset α) (x : α) :
  x ∈ antichain.join A B ↔ x ∈ A ∪ B ∧ ∀ y ∈ A ∪ B, x ≤ y → x = y :=
  begin
    rw [antichain.join, finset.mem_union],
    simp only [and_self_left, finset.mem_union, finset.mem_filter],
  end

theorem join_antichain (A B : finset α) :
  antichain (antichain.join A B) :=
begin
  intros a ha2 b hb2,

  rw antichain.mem_join_iff at ha2,
  rcases ha2 with ⟨hamem, ha⟩,

  rw antichain.mem_join_iff at hb2,
  rcases hb2 with ⟨hbmem, hb⟩,

  apply ha b hbmem,
end

theorem meet_antichain (A B : finset α) (ha : antichain A) :
  antichain (antichain.meet A B) := antichain.subset A (A ∩ B) ha (finset.inter_subset_left A B)


end
