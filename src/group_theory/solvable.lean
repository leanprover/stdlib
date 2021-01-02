/-
Copyright (c) 2020 Jordan Brown, Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning and Patrick Lutz
-/

import group_theory.abelianization

/-!
# Solvable Groups

In this file we introduce the notion of a solvable group. We define a solvable group as one whose
nth commutator is `1` for some `n`. This requires defining the commutator of two subgroups and
the nth commutator of a group.

## Main definitions

* `general_commutator H₁ H₂` : the commutator of the subgroups `H₁` and `H₂`
* `nth_commutator G n` : the `n`th commutator of `G`, defined by iterating `general_commutator`
  starting with the top subgroup
* `is_solvable G` : the group `G` is solvable
-/

open subgroup

variables {G : Type*} [group G]

section general_commutator

/-- The commutator of two subgroups `H₁` and `H₂`. -/
def general_commutator (H₁ : subgroup G) (H₂ : subgroup G) : subgroup G :=
subgroup.closure {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x}

instance general_commutator_normal (H₁ : subgroup G) (H₂ : subgroup G) [h₁ : H₁.normal]
  [h₂ : H₂.normal] : normal (general_commutator H₁ H₂) :=
begin
  let base : set G := {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x},
  suffices h_base : base = group.conjugates_of_set base,
  { dsimp only [general_commutator, ←base],
    rw h_base,
    exact subgroup.normal_closure_normal },
  apply set.subset.antisymm group.subset_conjugates_of_set,
  intros a h,
  rw group.mem_conjugates_of_set_iff at h,
  rcases h with ⟨b, ⟨c, hc, e, he, rfl⟩, d, rfl⟩,
  exact ⟨d * c * d⁻¹, h₁.conj_mem c hc d, d * e * d⁻¹, h₂.conj_mem e he d, by group⟩,
end

lemma general_commutator_mono {H₁ H₂ K₁ K₂ : subgroup G} (h₁ : H₁ ≤ K₁) (h₂ : H₂ ≤ K₂) :
  general_commutator H₁ H₂ ≤ general_commutator K₁ K₂ :=
begin
  apply closure_mono,
  rintros x ⟨p, hp, q, hq, rfl⟩,
  exact ⟨p, h₁ hp, q, h₂ hq, rfl⟩,
end

lemma general_commutator_eq_normal_closure_self (H₁ : subgroup G) (H₂ : subgroup G) [H₁.normal]
  [H₂.normal] : general_commutator H₁ H₂ = normal_closure (general_commutator H₁ H₂) :=
eq.symm normal_closure_eq_self_of_normal

lemma general_commutator_def' (H₁ H₂ : subgroup G) [H₁.normal] [H₂.normal] :
  general_commutator H₁ H₂ = normal_closure {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x} :=
by rw [general_commutator_eq_normal_closure_self, general_commutator,
  normal_closure_closure_eq_normal_closure]

end general_commutator

section nth_commutator

variables (G)

/-- The nth commutator of the group `G`, obtained by starting from the subgroup `⊤` and repeatedly
  taking the commutator of the previous subgroup with itself for `n` times. -/
def nth_commutator (n : ℕ) : subgroup G :=
nat.rec_on n (⊤ : subgroup G) (λ _ H, general_commutator H H)

@[simp] lemma nth_commutator_zero : nth_commutator G 0 = ⊤ := rfl

@[simp] lemma nth_commutator_succ (n : ℕ) :
  nth_commutator G (n + 1) = general_commutator (nth_commutator G n) (nth_commutator G n) := rfl

lemma nth_commutator_normal (n : ℕ) : (nth_commutator G n).normal :=
begin
  induction n with n ih,
  { exact subgroup.top_normal, },
  { haveI : (nth_commutator G n).normal := ih,
    rw nth_commutator_succ,
    exact general_commutator_normal (nth_commutator G n) (nth_commutator G n), }
end

lemma commutator_eq_general_commutator_top_top :
  commutator G = general_commutator (⊤ : subgroup G) (⊤ : subgroup G) :=
begin
  rw [commutator, general_commutator_def'],
  apply le_antisymm; apply normal_closure_mono,
  { exact λ x ⟨p, q, h⟩, ⟨p, mem_top p, q, mem_top q, h⟩, },
  { exact λ x ⟨p, _, q, _, h⟩, ⟨p, q, h⟩, }
end

lemma commutator_def' : commutator G = subgroup.closure {x : G | ∃ p q, p * q * p⁻¹ * q⁻¹ = x} :=
begin
  rw [commutator_eq_general_commutator_top_top, general_commutator],
  apply le_antisymm; apply closure_mono,
  { exact λ x ⟨p, _, q, _, h⟩, ⟨p, q, h⟩ },
  { exact λ x ⟨p, q, h⟩, ⟨p, mem_top p, q, mem_top q, h⟩ }
end

@[simp] lemma nth_commutator_one : nth_commutator G 1 = commutator G :=
eq.symm $ commutator_eq_general_commutator_top_top G

end nth_commutator

section solvable

variables (G)

/-- A group `G` is solvable if for some `n`, its nth commutator is trivial. We use this definition
  because it's the most convenient one to work with. -/
def is_solvable : Prop := ∃ n : ℕ, nth_commutator G n = (⊥ : subgroup G)

lemma is_solvable_of_comm {G : Type*} [comm_group G] : is_solvable G :=
begin
  use 1,
  rw [eq_bot_iff, nth_commutator_one],
  calc commutator G ≤ (monoid_hom.id G).ker : abelianization.commutator_subset_ker (monoid_hom.id G)
  ... = ⊥ : rfl,
end

end solvable
