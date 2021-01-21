/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import tactic

/-!
# Constructions involving sets of sets.

## Finite Intersections

We define a structure `has_finite_inter` which asserts that a set `S` of subsets of `α` is
closed under finite intersections.

We define `finite_inter_closure` which, given a set `S` of subsets of `α`, is the smallest
set of subsets of `α` which is closed under finite intersections.

`finite_inter_closure S` is endowed with a term of type `has_finite_inter` using
`finite_inter_closure_has_finite_inter`.

-/

variables {α : Type*} (S : set (set α))

/-- A structure encapsulating the fact that a set of sets is closed under finite intersection. -/
structure has_finite_inter :=
(univ_mem : set.univ ∈ S)
(inter_mem {s t} : s ∈ S → t ∈ S → s ∩ t ∈ S)

namespace has_finite_inter

-- Satisfying the inhabited linter...
instance : inhabited (has_finite_inter ({set.univ} : set (set α))) :=
⟨⟨by tauto, λ _ _ h1 h2, by finish⟩⟩

/-- The smallest set of sets containing `S` which is closed under finite intersections. -/
inductive finite_inter_closure : set (set α)
| basic {s} : s ∈ S → finite_inter_closure s
| univ : finite_inter_closure set.univ
| inter {s t} : finite_inter_closure s → finite_inter_closure t → finite_inter_closure (s ∩ t)

/-- Defines `has_finite_inter` for `finite_inter_closure S`. -/
def finite_inter_closure_has_finite_inter : has_finite_inter (finite_inter_closure S) :=
{ univ_mem := finite_inter_closure.univ,
  inter_mem := λ _ _, finite_inter_closure.inter }

variable {S}
lemma finite_inter_mem (cond : has_finite_inter S) (F : finset (set α)) :
  ↑F ⊆ S → ⋂₀ (↑F : set (set α)) ∈ S :=
begin
  classical,
  refine finset.induction_on F (λ _, _) _,
  { simp [cond.univ_mem] },
  { intros a s h1 h2 h3,
    suffices : a ∩ ⋂₀ ↑s ∈ S, by simpa,
    exact cond.inter_mem (h3 (finset.mem_insert_self a s))
                         (h2 $ λ x hx, h3 $ finset.mem_insert_of_mem hx) }
end

lemma finite_inter_closure_insert {A : set α} (cond : has_finite_inter S)
  (P ∈ finite_inter_closure (insert A S)) : P ∈ S ∨ ∃ Q ∈ S, P = A ∩ Q :=
begin
  induction H with S h T1 T2 _ _ h1 h2,
  { cases h,
    { exact or.inr ⟨set.univ, cond.univ_mem, by simpa⟩ },
    { exact or.inl h } },
  { exact or.inl cond.univ_mem },
  { rcases h1 with (h | ⟨Q, hQ, rfl⟩); rcases h2 with (i | ⟨R, hR, rfl⟩),
    { exact or.inl (cond.inter_mem h i) },
    { exact or.inr ⟨T1 ∩ R, cond.inter_mem h hR, by finish⟩ },
    { exact or.inr ⟨Q ∩ T2, cond.inter_mem hQ i, by finish⟩ },
    { exact or.inr ⟨Q ∩ R, cond.inter_mem hQ hR , by tidy⟩ } }
end

end has_finite_inter
