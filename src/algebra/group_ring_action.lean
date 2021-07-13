/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import group_theory.group_action.group
import data.equiv.ring
import deprecated.subring

/-!
# Group action on rings

This file defines the typeclass of monoid acting on semirings `mul_semiring_action M R`,
and the corresponding typeclass of invariant subrings.

Note that `algebra` does not satisfy the axioms of `mul_semiring_action`.

## Implementation notes

There is no separate typeclass for group acting on rings, group acting on fields, etc.
They are all grouped under `mul_semiring_action`.

## Tags

group action, invariant subring

-/

universes u v
open_locale big_operators

/-- Typeclass for multiplicative actions by monoids on semirings. -/
class mul_semiring_action (M : Type u) [monoid M] (R : Type v) [semiring R]
  extends distrib_mul_action M R :=
(smul_one : ∀ (g : M), (g • 1 : R) = 1)
(smul_mul : ∀ (g : M) (x y : R), g • (x * y) = (g • x) * (g • y))

export mul_semiring_action (smul_one)

/-- Typeclass for faithful multiplicative actions by monoids on semirings. -/
class faithful_mul_semiring_action (M : Type u) [monoid M] (R : Type v) [semiring R]
  extends mul_semiring_action M R :=
(eq_of_smul_eq_smul' : ∀ {m₁ m₂ : M}, (∀ r : R, m₁ • r = m₂ • r) → m₁ = m₂)

section semiring

variables (M G : Type u) [monoid M] [group G]
variables (A R S F : Type v) [add_monoid A] [semiring R] [comm_semiring S] [field F]

variables {M R}
lemma smul_mul' [mul_semiring_action M R] (g : M) (x y : R) :
  g • (x * y) = (g • x) * (g • y) :=
mul_semiring_action.smul_mul g x y

variables {M} (R)
theorem eq_of_smul_eq_smul [faithful_mul_semiring_action M R] {m₁ m₂ : M} :
  (∀ r : R, m₁ • r = m₂ • r) → m₁ = m₂ :=
faithful_mul_semiring_action.eq_of_smul_eq_smul'

variables (M R)

/-- Each element of the monoid defines a additive monoid homomorphism. -/
def distrib_mul_action.to_add_monoid_hom [distrib_mul_action M A] (x : M) : A →+ A :=
{ to_fun   := (•) x,
  map_zero' := smul_zero x,
  map_add' := smul_add x }

/-- Each element of the group defines an additive monoid isomorphism. -/
def distrib_mul_action.to_add_equiv [distrib_mul_action G A] (x : G) : A ≃+ A :=
{ .. distrib_mul_action.to_add_monoid_hom G A x,
  .. mul_action.to_perm_hom G A x }

/-- Each element of the group defines an additive monoid homomorphism. -/
def distrib_mul_action.hom_add_monoid_hom [distrib_mul_action M A] : M →* add_monoid.End A :=
{ to_fun := distrib_mul_action.to_add_monoid_hom M A,
  map_one' := add_monoid_hom.ext $ λ x, one_smul M x,
  map_mul' := λ x y, add_monoid_hom.ext $ λ z, mul_smul x y z }

/-- Each element of the monoid defines a semiring homomorphism. -/
def mul_semiring_action.to_semiring_hom [mul_semiring_action M R] (x : M) : R →+* R :=
{ map_one' := smul_one x,
  map_mul' := smul_mul' x,
  .. distrib_mul_action.to_add_monoid_hom M R x }

theorem to_semiring_hom_injective [faithful_mul_semiring_action M R] :
  function.injective (mul_semiring_action.to_semiring_hom M R) :=
λ m₁ m₂ h, eq_of_smul_eq_smul R $ λ r, ring_hom.ext_iff.1 h r

/-- Each element of the group defines a semiring isomorphism. -/
def mul_semiring_action.to_semiring_equiv [mul_semiring_action G R] (x : G) : R ≃+* R :=
{ .. distrib_mul_action.to_add_equiv G R x,
  .. mul_semiring_action.to_semiring_hom G R x }

section prod
variables [mul_semiring_action M R] [mul_semiring_action M S]

lemma list.smul_prod (g : M) (L : list R) : g • L.prod = (L.map $ (•) g).prod :=
monoid_hom.map_list_prod (mul_semiring_action.to_semiring_hom M R g : R →* R) L

lemma multiset.smul_prod (g : M) (m : multiset S) : g • m.prod = (m.map $ (•) g).prod :=
monoid_hom.map_multiset_prod (mul_semiring_action.to_semiring_hom M S g : S →* S) m

lemma smul_prod (g : M) {ι : Type*} (f : ι → S) (s : finset ι) :
  g • ∏ i in s, f i = ∏ i in s, g • f i :=
monoid_hom.map_prod (mul_semiring_action.to_semiring_hom M S g : S →* S) f s

end prod

section simp_lemmas

variables {M G A R}

attribute [simp] smul_one smul_mul' smul_zero smul_add

@[simp] lemma smul_inv' [mul_semiring_action M F] (x : M) (m : F) : x • m⁻¹ = (x • m)⁻¹ :=
(mul_semiring_action.to_semiring_hom M F x).map_inv _

@[simp] lemma smul_pow [mul_semiring_action M R] (x : M) (m : R) (n : ℕ) :
  x • m ^ n = (x • m) ^ n :=
begin
  induction n with n ih,
  { rw [pow_zero, pow_zero], exact smul_one x },
  { rw [pow_succ, pow_succ], exact (smul_mul' x m (m ^ n)).trans (congr_arg _ ih) }
end

end simp_lemmas

end semiring

section ring

variables (M : Type u) [monoid M] {R : Type v} [ring R] [mul_semiring_action M R]
variables (S : set R) [hS : fact (is_subring S)]
open mul_action

set_option old_structure_cmd false

include hS

/-- A subring invariant under the action. -/
structure is_invariant_subring : Prop :=
(smul_mem : ∀ (m : M) {x : R}, x ∈ S → m • x ∈ S)

variables [hMS : fact (is_invariant_subring M S)]

include hMS

local attribute [instance] subset.ring
instance is_invariant_subring.to_mul_semiring_action : mul_semiring_action M S :=
{ smul := λ m x, ⟨m • x, is_invariant_subring.smul_mem hMS.elim m x.2⟩,
  one_smul := λ s, subtype.eq $ one_smul M s,
  mul_smul := λ m₁ m₂ s, subtype.eq $ mul_smul m₁ m₂ s,
  smul_add := λ m s₁ s₂, subtype.eq $ smul_add m s₁ s₂,
  smul_zero := λ m, subtype.eq $ smul_zero m,
  smul_one := λ m, subtype.eq $ smul_one m,
  smul_mul := λ m s₁ s₂, subtype.eq $ smul_mul' m s₁ s₂ }

end ring
