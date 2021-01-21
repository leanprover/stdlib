/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import linear_algebra.finite_dimensional
import ring_theory.integral_closure

/-!
# Algebraic elements and algebraic extensions

An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial.
An R-algebra is algebraic over R if and only if all its elements are algebraic over R.
The main result in this file proves transitivity of algebraicity:
a tower of algebraic field extensions is algebraic.
-/

universe variables u v

open_locale classical
open polynomial

section
variables (R : Type u) {A : Type v} [comm_ring R] [ring A] [algebra R A]

/-- An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial. -/
def is_algebraic (x : A) : Prop :=
∃ p : polynomial R, p ≠ 0 ∧ aeval x p = 0

variables {R}

/-- A subalgebra is algebraic if all its elements are algebraic. -/
def subalgebra.is_algebraic (S : subalgebra R A) : Prop := ∀ x ∈ S, is_algebraic R x

variables (R A)

/-- An algebra is algebraic if all its elements are algebraic. -/
def algebra.is_algebraic : Prop := ∀ x : A, is_algebraic R x

variables {R A}

/-- A subalgebra is algebraic if and only if it is algebraic an algebra. -/
lemma subalgebra.is_algebraic_iff (S : subalgebra R A) :
  S.is_algebraic ↔ @algebra.is_algebraic R S _ _ (S.algebra) :=
begin
  delta algebra.is_algebraic subalgebra.is_algebraic,
  rw [subtype.forall'],
  apply forall_congr, rintro ⟨x, hx⟩,
  apply exists_congr, intro p,
  apply and_congr iff.rfl,
  have h : function.injective (S.val) := subtype.val_injective,
  conv_rhs { rw [← h.eq_iff, alg_hom.map_zero], },
  rw [← aeval_alg_hom_apply, S.val_apply]
end

/-- An algebra is algebraic if and only if it is algebraic as a subalgebra. -/
lemma algebra.is_algebraic_iff : algebra.is_algebraic R A ↔ (⊤ : subalgebra R A).is_algebraic :=
begin
  delta algebra.is_algebraic subalgebra.is_algebraic,
  simp only [algebra.mem_top, forall_prop_of_true, iff_self],
end

end

section zero_ne_one
variables (R : Type u) {A : Type v} [comm_ring R] [nontrivial R] [ring A] [algebra R A]

/-- An integral element of an algebra is algebraic.-/
lemma is_integral.is_algebraic {x : A} (h : is_integral R x) : is_algebraic R x :=
by { rcases h with ⟨p, hp, hpx⟩, exact ⟨p, hp.ne_zero, hpx⟩ }

end zero_ne_one

section field
variables (K : Type u) {A : Type v} [field K] [ring A] [algebra K A]

/-- An element of an algebra over a field is algebraic if and only if it is integral.-/
lemma is_algebraic_iff_is_integral {x : A} :
  is_algebraic K x ↔ is_integral K x :=
begin
  refine ⟨_, is_integral.is_algebraic K⟩,
  rintro ⟨p, hp, hpx⟩,
  refine ⟨_, monic_mul_leading_coeff_inv hp, _⟩,
  rw [← aeval_def, alg_hom.map_mul, hpx, zero_mul],
end

lemma is_algebraic_iff_is_integral' :
  algebra.is_algebraic K A ↔ algebra.is_integral K A :=
⟨λ h x, (is_algebraic_iff_is_integral K).mp (h x),
  λ h x, (is_algebraic_iff_is_integral K).mpr (h x)⟩

end field

namespace algebra
variables {K : Type*} {L : Type*} {A : Type*}
variables [field K] [field L] [comm_ring A]
variables [algebra K L] [algebra L A] [algebra K A] [is_scalar_tower K L A]

/-- If L is an algebraic field extension of K and A is an algebraic algebra over L,
then A is algebraic over K. -/
lemma is_algebraic_trans (L_alg : is_algebraic K L) (A_alg : is_algebraic L A) :
  is_algebraic K A :=
begin
  simp only [is_algebraic, is_algebraic_iff_is_integral] at L_alg A_alg ⊢,
  exact is_integral_trans L_alg A_alg,
end

/-- A field extension is algebraic if it is finite. -/
lemma is_algebraic_of_finite [finite : finite_dimensional K L] : is_algebraic K L :=
λ x, (is_algebraic_iff_is_integral _).mpr (is_integral_of_submodule_noetherian ⊤
  (is_noetherian_of_submodule_of_noetherian _ _ _ finite) x algebra.mem_top)

end algebra

variables {R S : Type*} [integral_domain R] [comm_ring S]

lemma exists_integral_multiple [algebra R S] {z : S} (hz : is_algebraic R z)
  (inj : ∀ x, algebra_map R S x = 0 → x = 0) :
  ∃ (x : integral_closure R S) (y ≠ (0 : integral_closure R S)),
    z * y = x :=
begin
  rcases hz with ⟨p, p_ne_zero, px⟩,
  set a := p.leading_coeff with a_def,
  have a_ne_zero : a ≠ 0 := mt polynomial.leading_coeff_eq_zero.mp p_ne_zero,
  have y_integral : is_integral R (algebra_map R S a) := is_integral_algebra_map,
  have x_integral : is_integral R (z * algebra_map R S a) :=
    ⟨ p.integral_normalization,
      monic_integral_normalization p_ne_zero,
      integral_normalization_aeval_eq_zero p_ne_zero px inj ⟩,
  refine ⟨⟨_, x_integral⟩, ⟨_, y_integral⟩, _, rfl⟩,
  exact λ h, a_ne_zero (inj _ (subtype.ext_iff_val.mp h))
end
section field

variables {K L : Type*} [field K] [field L] [algebra K L] (A : subalgebra K L)

lemma inv_eq_of_aeval_div_X_ne_zero {x : L} {p : polynomial K}
  (aeval_ne : aeval x (div_X p) ≠ 0) :
  x⁻¹ = aeval x (div_X p) / (aeval x p - algebra_map _ _ (p.coeff 0)) :=
begin
  rw [inv_eq_iff, inv_div, div_eq_iff, sub_eq_iff_eq_add, mul_comm],
  conv_lhs { rw ← div_X_mul_X_add p },
  rw [alg_hom.map_add, alg_hom.map_mul, aeval_X, aeval_C],
  exact aeval_ne
end

lemma inv_eq_of_root_of_coeff_zero_ne_zero {x : L} {p : polynomial K}
  (aeval_eq : aeval x p = 0) (coeff_zero_ne : p.coeff 0 ≠ 0) :
  x⁻¹ = - (aeval x (div_X p) / algebra_map _ _ (p.coeff 0)) :=
begin
  convert inv_eq_of_aeval_div_X_ne_zero (mt (λ h, (algebra_map K L).injective _) coeff_zero_ne),
  { rw [aeval_eq, zero_sub, div_neg] },
  rw ring_hom.map_zero,
  convert aeval_eq,
  conv_rhs { rw ← div_X_mul_X_add p },
  rw [alg_hom.map_add, alg_hom.map_mul, h, zero_mul, zero_add, aeval_C]
end

lemma subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero {x : A} {p : polynomial K}
  (aeval_eq : aeval x p = 0) (coeff_zero_ne : p.coeff 0 ≠ 0) : (x⁻¹ : L) ∈ A :=
begin
  have : (x⁻¹ : L) = aeval x (div_X p) / (aeval x p - algebra_map _ _ (p.coeff 0)),
  { rw [aeval_eq, submodule.coe_zero, zero_sub, div_neg],
    convert inv_eq_of_root_of_coeff_zero_ne_zero _ coeff_zero_ne,
    { rw subalgebra.aeval_coe },
    { simpa using aeval_eq } },
  rw [this, div_eq_mul_inv, aeval_eq, submodule.coe_zero, zero_sub, ← ring_hom.map_neg,
      ← ring_hom.map_inv],
  exact A.mul_mem (aeval x p.div_X).2 (A.algebra_map_mem _),
end

lemma subalgebra.inv_mem_of_algebraic {x : A} (hx : is_algebraic K (x : L)) : (x⁻¹ : L) ∈ A :=
begin
  obtain ⟨p, ne_zero, aeval_eq⟩ := hx,
  replace aeval_eq : aeval x p = 0,
  { rw ← submodule.coe_eq_zero,
    convert aeval_eq,
    exact is_scalar_tower.algebra_map_aeval K A L _ _ },
  revert ne_zero aeval_eq,
  refine p.rec_on_horner _ _ _,
  { intro h,
    contradiction },
  { intros p a hp ha ih ne_zero aeval_eq,
    refine A.inv_mem_of_root_of_coeff_zero_ne_zero aeval_eq _,
    rwa [coeff_add, hp, zero_add, coeff_C, if_pos rfl] },
  { intros p hp ih ne_zero aeval_eq,
    rw [alg_hom.map_mul, aeval_X, mul_eq_zero] at aeval_eq,
    cases aeval_eq with aeval_eq x_eq,
    { exact ih hp aeval_eq },
    { rw [x_eq, submodule.coe_zero, inv_zero],
      exact A.zero_mem } }
end

/-- In an algebraic extension L/K, an intermediate subalgebra is a field. -/
lemma subalgebra.is_field_of_algebraic (hKL : algebra.is_algebraic K L) : is_field A :=
{ mul_inv_cancel := λ a ha, ⟨
        ⟨a⁻¹, A.inv_mem_of_algebraic (hKL a)⟩,
        subtype.ext (mul_inv_cancel (mt submodule.coe_eq_zero.mp ha))⟩,
  .. subalgebra.integral_domain A }

end field
