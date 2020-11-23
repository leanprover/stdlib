/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/
import data.finset
import data.fintype.basic
import algebra.geom_sum

/-!
# Colex

We define the colex ordering for finite sets, and give a couple of important
lemmas and properties relating to it.

The colex ordering likes to avoid large values - it can be thought of on
`finset ℕ` as the "binary" ordering. That is, order A based on
`∑_{i ∈ A} 2^i`.
It's defined here a slightly more general way, requiring only `has_lt α` in
the definition of colex on `finset α`. In the context of the Kruskal-Katona
theorem, we are interested in particular on how colex behaves for sets of a
fixed size. If the size is 3, colex on ℕ starts
123, 124, 134, 234, 125, 135, 235, 145, 245, 345, ...

## Main statements
* `colex_hom`: strictly monotone functions preserve colex
* Colex order properties - linearity, decidability and so on.
* `max_colex`: if A < B in colex, and everything in B is < t, then everything
  in A is < t. This confirms the idea that an enumeration under colex will
  exhaust all sets using elements < t before allowing t to be included.
* `binary_iff`: colex for α = ℕ is the same as binary
  (this also proves binary expansions are unique)

## Notation
We define `<ᶜ` and `≤ᶜ` to denote colex ordering, useful in particular when
multiple orderings are available in context.

## Tags
colex, colexicographic, binary

## References
* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Todo
Show the subset ordering is a sub-relation of the colex ordering.
-/

variable {α : Type*}

open finset

/--
We define this type synonym to refer to the colexicographic ordering on finsets
rather than the natural subset ordering.
-/
@[derive inhabited]
def finset.colex (α) := finset α

/--
A convenience constructor to turn a `finset α` into a `finset.colex α`, useful in order to
use the colex ordering rather than the subset ordering.
-/
def finset.to_colex {α} (s : finset α) : finset.colex α := s

/--
`A` is less than `B` in the colex ordering if the largest thing that's not in both sets is in B.
In other words, max (A ▵ B) ∈ B (if the maximum exists).
-/
instance [has_lt α] : has_lt (finset.colex α) :=
⟨λ (A B : finset α), ∃ (k : α), (∀ {x}, k < x → (x ∈ A ↔ x ∈ B)) ∧ k ∉ A ∧ k ∈ B⟩

/-- We can define (≤) in the obvious way. -/
instance [has_lt α] : has_le (finset.colex α) :=
⟨λ A B, A < B ∨ A = B⟩

/-- The colex ordering on finsets. -/
def colex.lt [has_lt α] (A B : finset α) : Prop := A.to_colex < B.to_colex
/-- The colex ordering on finsets. -/
def colex.le [has_lt α] (A B : finset α) : Prop := A.to_colex ≤ B.to_colex

infix ` <ᶜ `:50 := colex.lt
infix ` ≤ᶜ `:50 := colex.le

lemma colex.lt_def [has_lt α] (A B : finset α) :
  A <ᶜ B ↔ ∃ k, (∀ {x}, k < x → (x ∈ A ↔ x ∈ B)) ∧ k ∉ A ∧ k ∈ B :=
iff.rfl
lemma colex.le_def [has_lt α] (A B : finset α) :
  A ≤ᶜ B ↔ A <ᶜ B ∨ A = B :=
iff.rfl

namespace colex

/-- Strictly monotone functions preserve the colex ordering. -/
lemma hom {β : Type*} [linear_order α] [decidable_eq β] [preorder β]
  {f : α → β} (h₁ : strict_mono f) (A B : finset α) :
  A.image f <ᶜ B.image f ↔ A <ᶜ B :=
begin
  simp only [colex.lt_def, not_exists, mem_image, exists_prop, not_and],
  split,
  { rintro ⟨k, z, q, k', _, rfl⟩,
    exact ⟨k', λ x hx, by simpa [h₁.injective] using z (h₁ hx), λ t, q _ t rfl, ‹k' ∈ B›⟩ },
  rintro ⟨k, z, ka, _⟩,
  refine ⟨f k, λ x hx, _, _, k, ‹k ∈ B›, rfl⟩,
  { split,
    any_goals {
      rintro ⟨x', hx', rfl⟩,
      refine ⟨x', _, rfl⟩,
      rwa ← z _ <|> rwa z _,
      rwa strict_mono.lt_iff_lt h₁ at hx } },
  { simp only [h₁.injective, function.injective.eq_iff],
    exact λ x hx, ne_of_mem_of_not_mem hx ka }
end

/-- A special case of `colex_hom` which is sometimes useful. -/
lemma colex_hom_fin {n : ℕ} (A B : finset (fin n)) :
  A.image subtype.val <ᶜ B.image subtype.val ↔ A <ᶜ B :=
colex.hom (λ x y k, k) _ _

instance [has_lt α] : is_irrefl (finset.colex α) (<) :=
⟨λ A h, exists.elim h (λ _ ⟨_,a,b⟩, a b)⟩

@[trans]
lemma lt_trans [linear_order α] {a b c : finset.colex α} :
  a < b → b < c → a < c :=
begin
  rintros ⟨k₁, k₁z, notinA, inB⟩ ⟨k₂, k₂z, notinB, inC⟩,
  cases lt_or_gt_of_ne (ne_of_mem_of_not_mem inB notinB),
  { refine ⟨k₂, _, by rwa k₁z h, inC⟩,
    intros x hx,
    rw ← k₂z hx,
    apply k₁z (trans h hx) },
  { refine ⟨k₁, _, notinA, by rwa ← k₂z h⟩,
    intros x hx,
    rw k₁z hx,
    apply k₂z (trans h hx) }
end

@[trans]
lemma le_trans [linear_order α] (a b c : finset.colex α) :
  a ≤ b → b ≤ c → a ≤ c :=
λ AB BC, AB.elim (λ k, BC.elim (λ t, or.inl (lt_trans k t)) (λ t, t ▸ AB)) (λ k, k.symm ▸ BC)

instance [linear_order α] : is_trans (finset.colex α) (<) := ⟨λ _ _ _, colex.lt_trans⟩
instance [linear_order α] : is_asymm (finset.colex α) (<) := by apply_instance

instance [linear_order α] : is_strict_order (finset.colex α) (<) := {}

lemma lt_trichotomy [linear_order α] (A B : finset.colex α) :
  A < B ∨ A = B ∨ B < A :=
begin
  classical,
  by_cases h₁ : (A = B),
  { right,
    left,
    assumption  },
  rcases (exists_max_image (A \ B ∪ B \ A) id _) with ⟨k, hk, z⟩,
  { simp only [mem_union, mem_sdiff] at hk,
    cases hk,
    { right,
      right,
      refine ⟨k, λ t th, _, hk.2, hk.1⟩,
      specialize z t,
      by_contra h₂,
      simp only [mem_union, mem_sdiff, id.def] at z,
      rw [not_iff, iff_iff_and_or_not_and_not, not_not, and_comm] at h₂,
      apply not_le_of_lt th (z h₂) },
    { left,
      refine ⟨k, λ t th, _, hk.2, hk.1⟩,
      specialize z t,
      by_contra h₃,
      simp only [mem_union, mem_sdiff, id.def] at z,
      rw [not_iff, iff_iff_and_or_not_and_not, not_not, and_comm, or_comm] at h₃,
      apply not_le_of_lt th (z h₃) }, },
  rw nonempty_iff_ne_empty,
  intro a,
  simp only [union_eq_empty_iff, sdiff_eq_empty_iff_subset] at a,
  apply h₁ (subset.antisymm a.1 a.2)
end

instance [linear_order α] : is_trichotomous (finset.colex α) (<) := ⟨lt_trichotomy⟩

-- It should be possible to do this computably but it doesn't seem to make any difference for now.
noncomputable instance [linear_order α] : linear_order (finset.colex α) :=
{ le_refl := λ A, or.inr rfl,
  le_trans := le_trans,
  le_antisymm := λ A B AB BA, AB.elim (λ k, BA.elim (λ t, (asymm k t).elim) (λ t, t.symm)) id,
  le_total := λ A B,
          (lt_trichotomy A B).elim3 (or.inl ∘ or.inl) (or.inl ∘ or.inr) (or.inr ∘ or.inl),
  decidable_le := classical.dec_rel _,
  ..finset.colex.has_le }

instance [linear_order α] : is_incomp_trans (finset.colex α) (<) :=
begin
  constructor,
  rintros A B C ⟨nAB, nBA⟩ ⟨nBC, nCB⟩,
  have: A = B := ((lt_trichotomy A B).resolve_left nAB).resolve_right nBA,
  have: B = C := ((lt_trichotomy B C).resolve_left nBC).resolve_right nCB,
  rw [‹A = B›, ‹B = C›, and_self],
  apply irrefl
end

instance [linear_order α] : is_strict_weak_order (finset.colex α) (<) := {}
instance [linear_order α] : is_strict_total_order (finset.colex α) (<) := {}

/-- Colex is an extension of the base ordering on α. -/
lemma singleton_lt_iff_lt [linear_order α] {r s : α} :
  ({r} : finset α) <ᶜ {s} ↔ r < s :=
begin
  rw colex.lt_def,
  simp only [mem_singleton, ← and_assoc, exists_eq_right],
  split,
  { rintro ⟨q, p⟩,
    apply lt_of_le_of_ne _ (ne.symm p),
    contrapose! p,
    rw (q p).1 rfl },
  { intro a,
    exact ⟨λ z hz, iff_of_false (ne_of_gt (trans hz a)) (ne_of_gt hz), ne_of_gt a⟩ }
end

/--
If A is before B in colex, and everything in B is small, then everything in A is small.
-/
lemma max_colex [linear_order α] {A B : finset α} (t : α) (h₁ : A <ᶜ B) (h₂ : ∀ x ∈ B, x < t) :
  ∀ x ∈ A, x < t :=
begin
  rw colex.lt_def at h₁,
  rcases h₁ with ⟨k, z, _, _⟩,
  intros x hx,
  apply lt_of_not_ge,
  intro a,
  refine not_lt_of_ge a (h₂ x _),
  rwa ← z,
  apply lt_of_lt_of_le (h₂ k ‹_›) a,
end

/-- If everything in A is less than k, we can bound the sum of powers. -/
-- TODO: This might belong somewhere else.
lemma binary_sum_nat {k : ℕ} {A : finset ℕ} (h₁ : ∀ {x}, x ∈ A → x < k) :
  A.sum (pow 2) < 2^k :=
begin
  apply lt_of_le_of_lt (sum_le_sum_of_subset (λ t, mem_range.2 ∘ h₁)),
  have z := geom_sum_mul_add 1 k,
  rw [geom_series, mul_one, one_add_one_eq_two] at z,
  rw ← z,
  apply nat.lt_succ_self,
end

/-- Colex doesn't care if you remove the other set -/
lemma colex_ignores_sdiff [has_lt α] [decidable_eq α] (A B : finset α) :
  A <ᶜ B ↔ A \ B <ᶜ B \ A :=
begin
  rw [colex.lt_def, colex.lt_def],
  apply exists_congr,
  intro k,
  simp only [mem_sdiff, not_and, not_not],
  split,
  { rintro ⟨z, kA, kB⟩,
    refine ⟨_, λ _, kB, kB, kA⟩,
    intros x hx,
    rw z hx },
  { rintro ⟨z, kAB, kB, kA⟩,
    refine ⟨_, kA, kB⟩,
    { intros x hx,
      specialize z hx,
      tauto } }
end

/-- For subsets of ℕ, we can show that colex is equivalent to binary. -/
lemma binary_iff (A B : finset ℕ) : A.sum (pow 2) < B.sum (pow 2) ↔ A <ᶜ B :=
begin
  have z : ∀ (A B : finset ℕ), A <ᶜ B → A.sum (pow 2) < B.sum (pow 2),
  { intros A B,
    rw [colex_ignores_sdiff, colex.lt_def],
    rintro ⟨k, z, kA, kB⟩,
    rw ← sdiff_union_inter A B,
    conv_rhs { rw ← sdiff_union_inter B A },
    rw [sum_union (disjoint_sdiff_inter _ _), sum_union (disjoint_sdiff_inter _ _),
        inter_comm, add_lt_add_iff_right],
    apply lt_of_lt_of_le (@binary_sum_nat k (A \ B) _),
    { apply single_le_sum (λ _ _, nat.zero_le _) kB },
    intros x hx,
    apply lt_of_le_of_ne (le_of_not_lt (λ kx, _)),
    { apply (ne_of_mem_of_not_mem hx kA) },
    specialize z kx,
    have := z.1 hx,
    rw mem_sdiff at this hx,
    exact hx.2 this.1 },
  refine ⟨λ h, (lt_trichotomy A B).resolve_right (λ h₁, h₁.elim _ (not_lt_of_gt h ∘ z _ _)), z A B⟩,
  rintro rfl,
  apply irrefl _ h
end

end colex
