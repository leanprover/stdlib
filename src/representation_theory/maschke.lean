/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.monoid_algebra
import algebra.char_p.invertible
import algebra.regular
import linear_algebra.basis

/-!
# Maschke's theorem

We prove **Maschke's theorem** for finite groups,
in the formulation that every submodule of a `k[G]` module has a complement,
when `k` is a field with `invertible (fintype.card G : k)`.

We do the core computation in greater generality.
For any `[comm_ring k]` in which  `[invertible (fintype.card G : k)]`,
and a `k[G]`-linear map `i : V → W` which admits a `k`-linear retraction `π`,
we produce a `k[G]`-linear retraction by
taking the average over `G` of the conjugates of `π`.

## Implementation Notes
* These results assume `invertible (fintype.card G : k)` which is equivalent to the more
familiar `¬(ring_char k ∣ fintype.card G)`. It is possible to convert between them using
`invertible_of_ring_char_not_dvd` and `not_ring_char_dvd_of_invertible`.


## Future work
It's not so far to give the usual statement, that every finite dimensional representation
of a finite group is semisimple (i.e. a direct sum of irreducibles).
-/

universes u

noncomputable theory
open module
open monoid_algebra
open_locale big_operators

section

-- At first we work with any `[comm_ring k]`, and add the assumption that
-- `[invertible (fintype.card G : k)]` when it is required.
variables {k : Type u} [comm_ring k] {G : Type u} [group G]

variables {V : Type u} [add_comm_group V] [module k V] [module (monoid_algebra k G) V]
variables [is_scalar_tower k (monoid_algebra k G) V]
variables {W : Type u} [add_comm_group W] [module k W] [module (monoid_algebra k G) W]
variables [is_scalar_tower k (monoid_algebra k G) W]

/-!
We now do the key calculation in Maschke's theorem.

Given `V → W`, an inclusion of `k[G]` modules,,
assume we have some retraction `π` (i.e. `∀ v, π (i v) = v`),
just as a `k`-linear map.
(When `k` is a field, this will be available cheaply, by choosing a basis.)

We now construct a retraction of the inclusion as a `k[G]`-linear map,
by the formula
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/

namespace linear_map

variables (π : W →ₗ[k] V)
include π

/--
We define the conjugate of `π` by `g`, as a `k`-linear map.
-/
def conjugate (g : G) : W →ₗ[k] V :=
((group_smul.linear_map k V g⁻¹).comp π).comp (group_smul.linear_map k W g)

variables (i : V →ₗ[monoid_algebra k G] W) (h : ∀ v : V, π (i v) = v)

section
include h

lemma conjugate_i (g : G) (v : V) : (conjugate π g) (i v) = v :=
begin
  dsimp [conjugate],
  simp only [←i.map_smul, h, ←mul_smul, single_mul_single, mul_one, mul_left_inv],
  change (1 : monoid_algebra k G) • v = v,
  simp,
end
end

variables (G) [fintype G]

/--
The sum of the conjugates of `π` by each element `g : G`, as a `k`-linear map.

(We postpone dividing by the size of the group as long as possible.)
-/
def sum_of_conjugates : W →ₗ[k] V :=
∑ g : G, π.conjugate g

/--
In fact, the sum over `g : G` of the conjugate of `π` by `g` is a `k[G]`-linear map.
-/
def sum_of_conjugates_equivariant : W →ₗ[monoid_algebra k G] V :=
monoid_algebra.equivariant_of_linear_of_comm (π.sum_of_conjugates G) (λ g v,
begin
  dsimp [sum_of_conjugates],
  simp only [linear_map.sum_apply, finset.smul_sum],
  dsimp [conjugate],
  conv_lhs {
    rw [←finset.univ_map_embedding (mul_right_embedding g⁻¹)],
    simp only [mul_right_embedding],
  },
  simp only [←mul_smul, single_mul_single, mul_inv_rev, mul_one, function.embedding.coe_fn_mk,
    finset.sum_map, inv_inv, inv_mul_cancel_right],
  recover,
end)

section
variables [inv : invertible (fintype.card G : k)]
include inv

/--
We construct our `k[G]`-linear retraction of `i` as
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/
def equivariant_projection : W →ₗ[monoid_algebra k G] V :=
⅟(fintype.card G : k) • (π.sum_of_conjugates_equivariant G)

include h

lemma equivariant_projection_condition (v : V) : (π.equivariant_projection G) (i v) = v :=
begin
  rw [equivariant_projection, smul_apply, sum_of_conjugates_equivariant,
    equivariant_of_linear_of_comm_apply, sum_of_conjugates],
  rw [linear_map.sum_apply],
  simp only [conjugate_i π i h],
  rw [finset.sum_const, finset.card_univ, nsmul_eq_smul_cast k,
    ←mul_smul, invertible.inv_of_mul_self, one_smul],
end
end
end linear_map
end

namespace char_zero

variables {k : Type u} [field k] {G : Type u} [fintype G] [group G] [char_zero k]

instance : invertible (fintype.card G : k) :=
invertible_of_ring_char_not_dvd (by simp [fintype.card_eq_zero_iff])

end char_zero

namespace monoid_algebra

-- Now we work over a `[field k]`.
variables {k : Type u} [field k] {G : Type u} [fintype G] [invertible (fintype.card G : k)]
variables [group G]
variables {V : Type u} [add_comm_group V] [module k V] [module (monoid_algebra k G) V]
variables [is_scalar_tower k (monoid_algebra k G) V]
variables {W : Type u} [add_comm_group W] [module k W] [module (monoid_algebra k G) W]
variables [is_scalar_tower k (monoid_algebra k G) W]

lemma exists_left_inverse_of_injective
  (f : V →ₗ[monoid_algebra k G] W) (hf : f.ker = ⊥) :
  ∃ (g : W →ₗ[monoid_algebra k G] V), g.comp f = linear_map.id :=
begin
  obtain ⟨φ, hφ⟩ := (f.restrict_scalars k).exists_left_inverse_of_injective
    (by simp only [hf, submodule.restrict_scalars_bot, linear_map.ker_restrict_scalars]),
  refine ⟨φ.equivariant_projection G, _⟩,
  ext v,
  simp only [linear_map.id_coe, id.def, linear_map.comp_apply],
  apply linear_map.equivariant_projection_condition,
  intro v,
  have := congr_arg linear_map.to_fun hφ,
  exact congr_fun this v
end

namespace submodule

lemma exists_is_compl
  (p : submodule (monoid_algebra k G) V) :
  ∃ q : submodule (monoid_algebra k G) V, is_compl p q :=
let ⟨f, hf⟩ := monoid_algebra.exists_left_inverse_of_injective p.subtype p.ker_subtype in
⟨f.ker, linear_map.is_compl_of_proj $ linear_map.ext_iff.1 hf⟩

/-- This also implies an instance `is_semisimple_module (monoid_algebra k G) V`. -/
instance is_complemented : is_complemented (submodule (monoid_algebra k G) V) :=
⟨exists_is_compl⟩

end submodule
end monoid_algebra
