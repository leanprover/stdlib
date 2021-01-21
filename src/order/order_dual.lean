/-
Copyright (c) 2020 Johan Commelin, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa
-/
import data.equiv.basic

/-!
# Initial lemmas to work with the `order_dual`

## Definitions
`to_dual` and `of_dual` the order reversing identity maps, bundled as equivalences.

## Basic Lemmas to convert between an order and its dual

This file is similar to algebra/group/type_tags.lean
-/

open function

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w} {r : α → α → Prop}

namespace order_dual

instance [nontrivial α] : nontrivial (order_dual α) := by delta order_dual; assumption

/-- `to_dual` is the identity function to the `order_dual` of a linear order.  -/
def to_dual : α ≃ order_dual α := ⟨id, id, λ h, rfl, λ h, rfl⟩

/-- `of_dual` is the identity function from the `order_dual` of a linear order.  -/
def of_dual : order_dual α ≃ α := to_dual.symm

@[simp] lemma to_dual_symm_eq : (@to_dual α).symm = of_dual := rfl

@[simp] lemma of_dual_symm_eq : (@of_dual α).symm = to_dual := rfl

@[simp] lemma to_dual_of_dual (a : order_dual α) : to_dual (of_dual a) = a := rfl
@[simp] lemma of_dual_to_dual (a : α) : of_dual (to_dual a) = a := rfl

@[simp] lemma to_dual_inj {a b : α} :
  to_dual a = to_dual b ↔ a = b := iff.rfl

@[simp] lemma to_dual_le_to_dual [has_le α] {a b : α} :
  to_dual a ≤ to_dual b ↔ b ≤ a := iff.rfl

@[simp] lemma to_dual_lt_to_dual [has_lt α] {a b : α} :
  to_dual a < to_dual b ↔ b < a := iff.rfl

@[simp] lemma of_dual_inj {a b : order_dual α} :
  of_dual a = of_dual b ↔ a = b := iff.rfl

@[simp] lemma of_dual_le_of_dual [has_le α] {a b : order_dual α} :
  of_dual a ≤ of_dual b ↔ b ≤ a := iff.rfl

@[simp] lemma of_dual_lt_of_dual [has_lt α] {a b : order_dual α} :
  of_dual a < of_dual b ↔ b < a := iff.rfl

lemma le_to_dual [has_le α] {a : order_dual α} {b : α} :
  a ≤ to_dual b ↔ b ≤ of_dual a := iff.rfl

lemma lt_to_dual [has_lt α] {a : order_dual α} {b : α} :
  a < to_dual b ↔ b < of_dual a := iff.rfl

lemma to_dual_le [has_le α] {a : α} {b : order_dual α} :
  to_dual a ≤ b ↔ of_dual b ≤ a := iff.rfl

lemma to_dual_lt [has_lt α] {a : α} {b : order_dual α} :
  to_dual a < b ↔ of_dual b < a := iff.rfl

end order_dual
