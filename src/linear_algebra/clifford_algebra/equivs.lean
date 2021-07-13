/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.basic
import data.complex.module

/-!
# Other constructions isomorphic to Clifford Algebras

This file contains isomorphisms showing that other types are equivalent to some `clifford_algebra`:

* `clifford_algebra_ring.equiv`: any ring is equivalent to a `clifford_algebra` over an empty
  vector space.
* `clifford_algebra_complex.equiv`: the `complex` numbers are equivalent to a
  `clifford_algebra` over a one-dimensional vector space with a quadratic form that satisfies
  `Q (ι Q 1) = -1`.

Future work:

* Isomorphism to the `quaternion`s over `ℝ × ℝ`, sending `i, j, k` to `(0, 1)`, `(1, 0)`, and
  `(1, 1)` (port from the `lean-ga` project).
-/

open clifford_algebra

namespace clifford_algebra_ring

variables {R : Type*} [comm_ring R]

@[simp]
lemma ι_eq_0 : ι (0 : quadratic_form R unit) = 0 :=
subsingleton.elim _ _

/-- The clifford algebra over a 0-dimensional vector space is isomorphic to its scalars. -/
def equiv : clifford_algebra (0 : quadratic_form R unit) ≃ₐ[R] R :=
alg_equiv.of_alg_hom
  (clifford_algebra.lift (0 : quadratic_form R unit) $
    ⟨0, λ m : unit, (zero_mul (0 : R)).trans (algebra_map R _).map_zero.symm⟩)
  (algebra.of_id R _)
  (by { ext x, exact (alg_hom.commutes _ x), })
  (by { ext : 1, rw [ι_eq_0, linear_map.comp_zero, linear_map.comp_zero], })

end clifford_algebra_ring

namespace clifford_algebra_complex

/-- The quadratic form sending elements to the negation of their square. -/
def Q : quadratic_form ℝ ℝ :=
-quadratic_form.lin_mul_lin linear_map.id linear_map.id

@[simp]
lemma Q_apply (r : ℝ) : Q r = - (r * r) := rfl

/-- Intermediate result for `clifford_algebra_complex.equiv`: clifford algebras over
`clifford_algebra_complex.Q` above can be converted to `ℂ`. -/
def to_complex : clifford_algebra Q →ₐ[ℝ] ℂ :=
clifford_algebra.lift Q ⟨linear_map.to_span_singleton _ _ complex.I, λ r, begin
  dsimp [linear_map.to_span_singleton, linear_map.id],
  rw smul_mul_smul,
  simp,
end⟩

@[simp]
lemma to_complex_ι (r : ℝ) : to_complex (clifford_algebra.ι Q r) = r • complex.I :=
clifford_algebra.lift_ι_apply _ _ r

/-- The clifford algebras over `clifford_algebra_complex.Q` is isomorphic as an `ℝ`-algebra to
`ℂ`. -/
@[simps]
def equiv : clifford_algebra Q ≃ₐ[ℝ] ℂ :=
alg_equiv.of_alg_hom to_complex
  (complex.lift ⟨clifford_algebra.ι Q 1, begin
    rw [clifford_algebra.ι_sq_scalar, Q_apply, one_mul, ring_hom.map_neg, ring_hom.map_one],
  end⟩)
  (begin
    ext1,
    dsimp only [alg_hom.comp_apply, subtype.coe_mk, alg_hom.id_apply, complex.lift_apply],
    rw [complex.lift_aux_apply_I, to_complex_ι, one_smul],
  end)
  (begin
    ext,
    dsimp only [linear_map.comp_apply, complex.lift_apply, subtype.coe_mk, alg_hom.id_apply,
      alg_hom.to_linear_map_apply, alg_hom.comp_apply],
    rw [to_complex_ι, one_smul, complex.lift_aux_apply_I],
  end)

end clifford_algebra_complex
