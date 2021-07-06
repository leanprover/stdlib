/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.free
import algebra.lie.quotient

/-!
# Lie algebras from Cartan matrices

Split semi-simple Lie algebras are uniquely determined by their Cartan matrix. Indeed, if `A` is
an `l × l` Cartan matrix, the corresponding Lie algebra may be obtained as the Lie algebra on
`3l` generators: $H_1, H_2, \ldots H_l, E_1, E_2, \ldots, E_l, F_1, F_2, \ldots, F_l$
subject to the following relations:
$$
\begin{align}
  [H_i, H_j] &= 0\\
  [E_i, F_i] &= H_i \quad\mbox{ and }\quad [E_i, F_j] = 0 \quad\mbox{if $i ≠ j$}\\
  [H_i, E_j] &= A_{ij}E_j\\
  [H_i, F_j] &= -A_{ij}F_j\\
  ad(E_i)^{1 - A_{ij}}(E_j) &= 0 \quad\mbox{if $i \ne j$}\\
  ad(F_i)^{1 - A_{ij}}(F_j) &= 0 \quad\mbox{if $i \ne j$}\\
\end{align}
$$

In this file we provide the above construction. It is defined for any matrix of integers but the
results for non-Cartan matrices should be regarded as junk.

## Main definitions

  * `lie_algebra.from_cartan_matrix`

## Tags

lie algebra, semi-simple, cartan matrix
-/

universes u v w

noncomputable theory

variables (R : Type u) {B : Type v} [comm_ring R] [decidable_eq B] [fintype B]
variables (A : matrix B B ℤ)

namespace cartan_matrix

variables (B)

/-- The generators of the free Lie algebra from which we construct the Lie algebra of a Cartan
matrix as a quotient. -/
inductive generators
| H : B → generators
| E : B → generators
| F : B → generators

instance [inhabited B] : inhabited (generators B) := ⟨generators.H $ default B⟩

variables {B}

namespace relations

local notation `H` := free_lie_algebra.of R ∘ generators.H
local notation `E` := free_lie_algebra.of R ∘ generators.E
local notation `F` := free_lie_algebra.of R ∘ generators.F
local notation `ad` := lie_algebra.ad R (free_lie_algebra R (generators B))

/-- The terms correpsonding to the `⁅H, H⁆`-relations. -/
def HH : B × B → free_lie_algebra R (generators B) := function.uncurry $ λ i j,
⁅H i, H j⁆

/-- The terms correpsonding to the `⁅E, F⁆`-relations. -/
def EF : B × B → free_lie_algebra R (generators B) := function.uncurry $ λ i j,
if i = j then ⁅E i, F i⁆ - H i else ⁅E i, F j⁆

/-- The terms correpsonding to the `⁅H, E⁆`-relations. -/
def HE : B × B → free_lie_algebra R (generators B) := function.uncurry $ λ i j,
⁅H i, E j⁆ - (A i j) • E j

/-- The terms correpsonding to the `⁅H, F⁆`-relations. -/
def HF : B × B → free_lie_algebra R (generators B) := function.uncurry $ λ i j,
⁅H i, F j⁆ + (A i j) • F j

/-- The terms correpsonding to the `ad E`-relations.

Note that we use `int.to_nat` so that we can take the power and that we do not bother
restricting to the case `i ≠ j` since these relations are zero anyway. We also defensively
ensure this with `ad_E_of_eq_eq_zero`. -/
def ad_E : B × B → free_lie_algebra R (generators B) := function.uncurry $ λ i j,
(ad (E i))^(-A i j).to_nat $ ⁅E i, E j⁆

/-- The terms correpsonding to the `ad F`-relations.

See also `ad_E` docstring. -/
def ad_F : B × B → free_lie_algebra R (generators B) := function.uncurry $ λ i j,
(ad (F i))^(-A i j).to_nat $ ⁅F i, F j⁆

private lemma ad_E_of_eq_eq_zero (i : B) (h : A i i = 2) : ad_E R A ⟨i, i⟩ = 0 :=
have h' : (-2 : ℤ).to_nat = 0, { refl, },
by simp [ad_E, h, h']

private lemma ad_F_of_eq_eq_zero (i : B) (h : A i i = 2) : ad_F R A ⟨i, i⟩ = 0 :=
have h' : (-2 : ℤ).to_nat = 0, { refl, },
by simp [ad_F, h, h']

/-- The union of all the relations as a subset of the free Lie algebra. -/
def to_set : set (free_lie_algebra R (generators B)) :=
(set.range $ HH R) ∪
(set.range $ EF R) ∪
(set.range $ HE R A) ∪
(set.range $ HF R A) ∪
(set.range $ ad_E R A) ∪
(set.range $ ad_F R A)

/-- The ideal of the free Lie algebra generated by the relations. -/
def to_ideal : lie_ideal R (free_lie_algebra R (generators B)) :=
lie_submodule.lie_span R _ $ to_set R A

end relations

end cartan_matrix

/-- The Lie algebra corresponding to a Cartan matrix.

Note that it is defined for any matrix of integers. Its value for non-Cartan matrices should be
regarded as junk. -/
@[derive [lie_ring, lie_algebra R]]
def matrix.to_lie_algebra := (cartan_matrix.relations.to_ideal R A).quotient

instance (A : matrix B B ℤ) : inhabited (matrix.to_lie_algebra R A) := ⟨0⟩
