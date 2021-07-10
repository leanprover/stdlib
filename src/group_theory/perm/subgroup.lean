/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import group_theory.perm.basic
import data.fintype.basic
import group_theory.subgroup
/-!
# Lemmas about subgroups within the permutations (self-equivalences) of a type `α`

This file provides extra lemmas about some `subgroup`s that exist within `equiv.perm α`.
`group_theory.subgroup` depends on `group_theory.perm.basic`, so these need to be in a separate
file.

It also provides decidable instances on membership in these subgroups, since
`monoid_hom.decidable_mem_range` cannot be inferred without the help of a lambda.
The presence of these instances induces a `fintype` instance on the `quotient_group.quotient` of
these subgroups.
-/

namespace equiv
namespace perm

universes u

instance sum_congr_hom.decidable_mem_range {α β : Type*}
  [decidable_eq α] [decidable_eq β] [fintype α] [fintype β] :
  decidable_pred (∈ (sum_congr_hom α β).range) :=
λ x, infer_instance

@[simp]
lemma sum_congr_hom.card_range {α β : Type*}
  [fintype (sum_congr_hom α β).range] [fintype (perm α × perm β)] :
  fintype.card (sum_congr_hom α β).range = fintype.card (perm α × perm β) :=
fintype.card_eq.mpr ⟨(of_injective (sum_congr_hom α β) sum_congr_hom_injective).symm⟩

instance sigma_congr_right_hom.decidable_mem_range {α : Type*} {β : α → Type*}
  [decidable_eq α] [∀ a, decidable_eq (β a)] [fintype α] [∀ a, fintype (β a)] :
  decidable_pred (∈ (sigma_congr_right_hom β).range) :=
λ x, infer_instance

@[simp]
lemma sigma_congr_right_hom.card_range {α : Type*} {β : α → Type*}
  [fintype (sigma_congr_right_hom β).range] [fintype (Π a, perm (β a))] :
  fintype.card (sigma_congr_right_hom β).range = fintype.card (Π a, perm (β a)) :=
fintype.card_eq.mpr ⟨(of_injective (sigma_congr_right_hom β) sigma_congr_right_hom_injective).symm⟩

instance subtype_congr_hom.decidable_mem_range {α : Type*} (p : α → Prop) [decidable_pred p]
  [fintype (perm {a // p a} × perm {a // ¬ p a})] [decidable_eq (perm α)] :
  decidable_pred (∈ (subtype_congr_hom p).range) :=
λ x, infer_instance

@[simp]
lemma subtype_congr_hom.card_range {α : Type*} (p : α → Prop) [decidable_pred p]
  [fintype (subtype_congr_hom p).range] [fintype (perm {a // p a} × perm {a // ¬ p a})] :
  fintype.card (subtype_congr_hom p).range = fintype.card (perm {a // p a} × perm {a // ¬ p a}) :=
fintype.card_eq.mpr ⟨(of_injective (subtype_congr_hom p) (subtype_congr_hom_injective p)).symm⟩

end perm
end equiv
