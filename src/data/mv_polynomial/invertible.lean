/-
Copyright (c) 2020 Johan Commelin and Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin and Robert Y. Lewis
-/

import ring_theory.algebra_tower

/-!
# Invertible polynomials

This file is a stub containing some basic facts about invertible elements in the ring of polynomials.
-/

open mv_polynomial

noncomputable instance mv_polynomial.invertible_C
  (σ : Type*) {R : Type*} [comm_semiring R] (r : R) [invertible r] :
  invertible (C r : mv_polynomial σ R) :=
invertible.map C.to_monoid_hom _

/-- A natural number that is invertible when coerced to a commutative semiring `R` is also invertible
when coerced to any polynomial ring with rational coefficients.

Short-cut for typeclass resolution. -/
noncomputable instance mv_polynomial.invertible_coe_nat
  (σ R : Type*) (p : ℕ) [comm_semiring R] [invertible (p : R)] :
  invertible (p : mv_polynomial σ R) :=
is_scalar_tower.invertible_algebra_coe_nat R _ _
