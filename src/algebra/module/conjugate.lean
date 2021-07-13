/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import algebra.module.basic
import ring_theory.ring_invo
import data.complex.is_R_or_C

/-!
# Conjugate semimodules

Given a `semimodule R E` with `R` a commutative semiring, we define its conjugate semimodule with
respect to a ring involution `I : R ≃+* Rᵒᵖ`, in which the scalar product is defined as
`r • (to_conj I x) = to_conj ((I r) • x)`. This is a generalization of the complex conjugate
vector space, where the ring involution is the complex conjugation. Since this is an important
special case, we define also `conj_semimodule 𝕜 E` with `[is_R_or_C 𝕜]` to avoid having to deal
with the ring involution explicitly.

## Implementation notes

The conjugate semimodule is defined as a copy of the original type, with conversions having to be
done explicitly via `to_conj` and `from_conj`, as for the opposite type. Facts that are specific
to normed spaces and inner product spaces are defined in `analysis/normed_space/conjugate.lean`.

## References

* https://en.wikipedia.org/wiki/Complex_conjugate_vector_space

## Tags

conjugate semimodule, conjugate vector space
-/

variables {R : Type*} [comm_semiring R]

/-- The conjugate of a semimodule `E` with respect to a ring involution `I`. -/
@[derive [add_comm_monoid], nolint unused_arguments]
def conjugate_semimodule (I : R ≃+* Rᵒᵖ) (E : Type*) [add_comm_monoid E] := E

instance {I : R ≃+* Rᵒᵖ} {E : Type*} [add_comm_monoid E] : inhabited (conjugate_semimodule I E) :=
  ⟨0⟩

/-- The `is_R_or_C` complex conjugate semimodule of `E` -/
abbreviation conj_semimodule (𝕜 : Type*) [is_R_or_C 𝕜] (E : Type*) [add_comm_monoid E] :=
  conjugate_semimodule (is_R_or_C.conj_to_ring_equiv 𝕜) E

namespace conjugate_semimodule

variables {E : Type*}  [add_comm_monoid E]

/-- The equivalence between `E` and its conjugate semimodule. -/
@[nolint unused_arguments] def conj_equiv (I : R ≃+* Rᵒᵖ) : E ≃+ conjugate_semimodule I E :=
{ to_fun := id,
  inv_fun := id,
  left_inv := λ x, rfl,
  right_inv := λ x, rfl,
  map_add' := λ x y, rfl }

variables {I : R ≃+* Rᵒᵖ}

instance [has_scalar R E] : has_scalar R (conjugate_semimodule I E) :=
{ smul := λ r x, conj_equiv I ((I r).unop • ((conj_equiv I).symm  x)) }

instance [mul_action R E] : mul_action R (conjugate_semimodule I E) :=
{ one_smul := λ x, by { change conj_equiv I ((I 1).unop • ((conj_equiv I).symm x)) = x, simp },
  mul_smul := λ x y z,
  begin
    change conj_equiv I( (I (x * y)).unop • ((conj_equiv I).symm z))
      = conj_equiv I
       ((I x).unop • ((conj_equiv I).symm ( conj_equiv I ((I y).unop • ((conj_equiv I).symm z)) ))),
    simp [mul_comm, mul_smul],
  end }

instance [distrib_mul_action R E] : distrib_mul_action R (conjugate_semimodule I E) :=
{ smul_add := λ r x y,
  begin
    change conj_equiv I ((I r).unop • ((conj_equiv I).symm (x + y)))
      = conj_equiv I
       ((I r).unop • ((conj_equiv I).symm x)) + conj_equiv I ((I r).unop • ((conj_equiv I).symm y)),
    simp [smul_add],
  end,
  smul_zero := λ r, by { change conj_equiv I ((I r).unop • ((conj_equiv I).symm 0)) = 0, simp} }

instance [semimodule R E] : semimodule R (conjugate_semimodule I E) :=
{ add_smul := λ r s x,
  begin
    change conj_equiv I ((I (r + s)).unop • ((conj_equiv I).symm x))
      = conj_equiv I ((I r).unop • ((conj_equiv I).symm x))
      + conj_equiv I ((I s).unop • ((conj_equiv I).symm x)),
    simp [add_smul],
  end,
  zero_smul := λ x, by { change conj_equiv I ((I 0).unop • ((conj_equiv I).symm x)) = 0,
                          simp [zero_smul] } }

end conjugate_semimodule

namespace conj_semimodule
open is_R_or_C

variables {𝕜 : Type*} [is_R_or_C 𝕜]
variables {E : Type*} [add_comm_monoid E] [semimodule 𝕜 E]
local postfix `†`:100 := @conj 𝕜 _
local notation `I` := conj_to_ring_equiv 𝕜

variables (𝕜)
/-- The equivalence between `E` and its conjugate space -/
@[nolint unused_arguments] def conj_equiv : E ≃+ conj_semimodule 𝕜 E :=
  conjugate_semimodule.conj_equiv I

variables {𝕜}

lemma smul_def {r : 𝕜} {x : E} : conj_equiv 𝕜 (r • x) = r† • (conj_equiv 𝕜 x) :=
by simp [conj_equiv, has_scalar.smul]

lemma smul_def' {r : 𝕜} {x : conj_semimodule 𝕜 E} :
  (conj_equiv 𝕜).symm (r • x) = r† • ((conj_equiv 𝕜).symm x) :=
by simp [conj_equiv, has_scalar.smul]

end conj_semimodule
