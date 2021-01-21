/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import data.equiv.encodable.basic

/-!
# Order ideals, cofinal sets, and the Rasiowa–Sikorski lemma

## Main definitions

We work with a preorder `P` throughout.

- `ideal P`: the type of upward directed, downward closed subsets of `P`.
             Dual to the notion of a filter on a preorder.
- `cofinal P`: the type of subsets of `P` containing arbitrarily large elements.
               Dual to the notion of 'dense set' used in forcing.
- `ideal_of_cofinals p 𝒟`, where `p : P`, and `𝒟` is a countable family of cofinal
  subsets of P: an ideal in `P` which contains `p` and intersects every set in `𝒟`.

## References

- https://en.wikipedia.org/wiki/Ideal_(order_theory)
- https://en.wikipedia.org/wiki/Cofinal_(mathematics)
- https://en.wikipedia.org/wiki/Rasiowa–Sikorski_lemma

Note that for the Rasiowa–Sikorski lemma, Wikipedia uses the opposite ordering on `P`,
in line with most presentations of forcing.

## Tags

ideal, cofinal, dense, countable, generic

-/

namespace order

variables {P : Type*} [preorder P]

/-- An ideal on a preorder `P` is a subset of `P` that is
  - nonempty
  - upward directed
  - downward closed. -/
structure ideal (P) [preorder P] :=
(carrier   : set P)
(nonempty  : carrier.nonempty)
(directed  : directed_on (≤) carrier)
(mem_of_le : ∀ {x y : P}, x ≤ y → y ∈ carrier → x ∈ carrier)

namespace ideal

/-- The smallest ideal containing a given element. -/
def principal (p : P) : ideal P :=
{ carrier   := { x | x ≤ p },
  nonempty  := ⟨p, le_refl _⟩,
  directed  := λ x hx y hy, ⟨p, le_refl _, hx, hy⟩,
  mem_of_le := λ x y hxy hy, le_trans hxy hy, }

instance [inhabited P] : inhabited (ideal P) :=
⟨ideal.principal $ default P⟩

instance : has_mem P (ideal P) := ⟨λ x I, x ∈ I.carrier⟩

end ideal

/-- For a preorder `P`, `cofinal P` is the type of subsets of `P`
  containing arbitrarily large elements. They are the dense sets in
  the topology whose open sets are terminal segments. -/
structure cofinal (P) [preorder P] :=
(carrier : set P)
(mem_gt  : ∀ x : P, ∃ y ∈ carrier, x ≤ y)

instance : inhabited (cofinal P) :=
⟨{ carrier := set.univ, mem_gt := λ x, ⟨x, trivial, le_refl _⟩}⟩

instance : has_mem P (cofinal P) := ⟨λ x D, x ∈ D.carrier⟩

namespace cofinal

variables (D : cofinal P) (x : P)
/-- A (noncomputable) element of a cofinal set lying above a given element. -/
noncomputable def above : P := classical.some $ D.mem_gt x

lemma above_mem : D.above x ∈ D :=
exists.elim (classical.some_spec $ D.mem_gt x) $ λ a _, a

lemma le_above : x ≤ D.above x :=
exists.elim (classical.some_spec $ D.mem_gt x) $ λ _ b, b

end cofinal

section ideal_of_cofinals

variables (p : P) {ι : Type*} [encodable ι] (𝒟 : ι → cofinal P)

/-- Given a starting point, and a countable family of cofinal sets,
  this is an increasing sequence that intersects each cofinal set. -/
noncomputable def sequence_of_cofinals : ℕ → P
| 0 := p
| (n+1) := match encodable.decode ι n with
           | none   := sequence_of_cofinals n
           | some i := (𝒟 i).above (sequence_of_cofinals n)
           end

lemma sequence_of_cofinals.monotone : monotone (sequence_of_cofinals p 𝒟) :=
by { apply monotone_of_monotone_nat, intros n, dunfold sequence_of_cofinals,
  cases encodable.decode ι n, { refl }, { apply cofinal.le_above }, }

lemma sequence_of_cofinals.encode_mem (i : ι) :
  sequence_of_cofinals p 𝒟 (encodable.encode i + 1) ∈ 𝒟 i :=
by { dunfold sequence_of_cofinals, rw encodable.encodek, apply cofinal.above_mem, }

/-- Given an element `p : P` and a family `𝒟` of cofinal subsets of a preorder `P`,
  indexed by a countable type, `ideal_of_cofinals p 𝒟` is an ideal in `P` which
  - contains `p`, according to `mem_ideal_of_cofinals p 𝒟`, and
  - intersects every set in `𝒟`, according to `cofinal_meets_ideal_of_cofinals p 𝒟`.

  This proves the Rasiowa–Sikorski lemma. -/
def ideal_of_cofinals : ideal P :=
{ carrier   := { x : P | ∃ n, x ≤ sequence_of_cofinals p 𝒟 n },
  nonempty  := ⟨p, 0, le_refl _⟩,
  directed  := λ x ⟨n, hn⟩ y ⟨m, hm⟩,
               ⟨_, ⟨max n m, le_refl _⟩,
               le_trans hn $ sequence_of_cofinals.monotone p 𝒟 (le_max_left _ _),
               le_trans hm $ sequence_of_cofinals.monotone p 𝒟 (le_max_right _ _) ⟩,
  mem_of_le := λ x y hxy ⟨n, hn⟩, ⟨n, le_trans hxy hn⟩, }

lemma mem_ideal_of_cofinals : p ∈ ideal_of_cofinals p 𝒟 := ⟨0, le_refl _⟩

/-- `ideal_of_cofinals p 𝒟` is `𝒟`-generic. -/
lemma cofinal_meets_ideal_of_cofinals (i : ι) : ∃ x : P, x ∈ 𝒟 i ∧ x ∈ ideal_of_cofinals p 𝒟 :=
⟨_, sequence_of_cofinals.encode_mem p 𝒟 i, _, le_refl _⟩

end ideal_of_cofinals

end order
