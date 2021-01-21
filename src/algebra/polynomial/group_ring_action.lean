/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import data.polynomial.monic

/-!
# Group action on rings applied to polynomials

This file contains instances and definitions relating `mul_semiring_action` to `polynomial`.
-/

variables (M : Type*) [monoid M]

namespace polynomial

variables (R : Type*) [semiring R]

noncomputable instance [mul_semiring_action M R] : mul_semiring_action M (polynomial R) :=
{ smul := λ m, map $ mul_semiring_action.to_semiring_hom M R m,
  one_smul := λ p, by { ext n, erw coeff_map, exact one_smul M (p.coeff n) },
  mul_smul := λ m n p, by { ext i,
    iterate 3 { rw coeff_map (mul_semiring_action.to_semiring_hom M R _) },
    exact mul_smul m n (p.coeff i) },
  smul_add := λ m p q, map_add (mul_semiring_action.to_semiring_hom M R m),
  smul_zero := λ m, map_zero (mul_semiring_action.to_semiring_hom M R m),
  smul_one := λ m, map_one (mul_semiring_action.to_semiring_hom M R m),
  smul_mul := λ m p q, map_mul (mul_semiring_action.to_semiring_hom M R m), }

noncomputable instance [faithful_mul_semiring_action M R] :
  faithful_mul_semiring_action M (polynomial R) :=
{ eq_of_smul_eq_smul' := λ m₁ m₂ h, eq_of_smul_eq_smul R $ λ s, C_inj.1 $
    calc  C (m₁ • s)
        = m₁ • C s : (map_C $ mul_semiring_action.to_semiring_hom M R m₁).symm
    ... = m₂ • C s : h (C s)
    ... = C (m₂ • s) : map_C _,
  .. polynomial.mul_semiring_action M R }

variables {M R}

variables [mul_semiring_action M R]

@[simp] lemma coeff_smul' (m : M) (p : polynomial R) (n : ℕ) :
  (m • p).coeff n = m • p.coeff n :=
coeff_map _ _

@[simp] lemma smul_C (m : M) (r : R) : m • C r = C (m • r) :=
map_C _

@[simp] lemma smul_X (m : M) : (m • X : polynomial R) = X :=
map_X _

variables (S : Type*) [comm_semiring S] [mul_semiring_action M S]

theorem smul_eval_smul (m : M) (f : polynomial S) (x : S) :
  (m • f).eval (m • x) = m • f.eval x :=
polynomial.induction_on f
  (λ r, by rw [smul_C, eval_C, eval_C])
  (λ f g ihf ihg, by rw [smul_add, eval_add, ihf, ihg, eval_add, smul_add])
  (λ n r ih, by rw [smul_mul', smul_pow, smul_C, smul_X, eval_mul, eval_C, eval_pow, eval_X,
      eval_mul, eval_C, eval_pow, eval_X, smul_mul', smul_pow])

variables (G : Type*) [group G]

theorem eval_smul' [mul_semiring_action G S] (g : G) (f : polynomial S) (x : S) :
  f.eval (g • x) = g • (g⁻¹ • f).eval x :=
by rw [← smul_eval_smul, smul_inv_smul]

theorem smul_eval [mul_semiring_action G S] (g : G) (f : polynomial S) (x : S) :
  (g • f).eval x = g • f.eval (g⁻¹ • x) :=
by rw [← smul_eval_smul, smul_inv_smul]

end polynomial

section comm_ring

variables (G : Type*) [group G] [fintype G]
variables (R : Type*) [comm_ring R] [mul_semiring_action G R]
open mul_action
open_locale classical

/-- the product of `(X - g • x)` over distinct `g • x`. -/
noncomputable def prod_X_sub_smul (x : R) : polynomial R :=
(finset.univ : finset (quotient_group.quotient $ mul_action.stabilizer G x)).prod $
λ g, polynomial.X - polynomial.C (of_quotient_stabilizer G x g)

theorem prod_X_sub_smul.monic (x : R) : (prod_X_sub_smul G R x).monic :=
polynomial.monic_prod_of_monic _ _ $ λ g _, polynomial.monic_X_sub_C _

theorem prod_X_sub_smul.eval (x : R) : (prod_X_sub_smul G R x).eval x = 0 :=
(finset.prod_hom _ (polynomial.eval x)).symm.trans $
  finset.prod_eq_zero (finset.mem_univ $ quotient_group.mk 1) $
  by rw [of_quotient_stabilizer_mk, one_smul, polynomial.eval_sub, polynomial.eval_X,
    polynomial.eval_C, sub_self]

theorem prod_X_sub_smul.smul (x : R) (g : G) :
  g • prod_X_sub_smul G R x = prod_X_sub_smul G R x :=
(smul_prod _ _ _ _ _).trans $ finset.prod_bij (λ g' _, g • g') (λ _ _, finset.mem_univ _)
  (λ g' _, by rw [of_quotient_stabilizer_smul, smul_sub, polynomial.smul_X, polynomial.smul_C])
  (λ _ _ _ _ H, (mul_action.bijective g).1 H)
  (λ g' _, ⟨g⁻¹ • g', finset.mem_univ _, by rw [smul_smul, mul_inv_self, one_smul]⟩)

theorem prod_X_sub_smul.coeff (x : R) (g : G) (n : ℕ) :
  g • (prod_X_sub_smul G R x).coeff n =
  (prod_X_sub_smul G R x).coeff n :=
by rw [← polynomial.coeff_smul', prod_X_sub_smul.smul]

end comm_ring

namespace mul_semiring_action_hom
variables {M}
variables {P : Type*} [comm_semiring P] [mul_semiring_action M P]
variables {Q : Type*} [comm_semiring Q] [mul_semiring_action M Q]
open polynomial

/-- An equivariant map induces an equivariant map on polynomials. -/
protected noncomputable def polynomial (g : P →+*[M] Q) : polynomial P →+*[M] polynomial Q :=
{ to_fun := map g,
  map_smul' := λ m p, polynomial.induction_on p
    (λ b, by rw [smul_C, map_C, coe_fn_coe, g.map_smul, map_C, coe_fn_coe, smul_C])
    (λ p q ihp ihq, by rw [smul_add, polynomial.map_add, ihp, ihq, polynomial.map_add, smul_add])
    (λ n b ih, by rw [smul_mul', smul_C, smul_pow, smul_X, polynomial.map_mul, map_C,
        polynomial.map_pow, map_X, coe_fn_coe, g.map_smul, polynomial.map_mul, map_C,
        polynomial.map_pow, map_X, smul_mul', smul_C, smul_pow, smul_X, coe_fn_coe]),
  map_zero' := polynomial.map_zero g,
  map_add' := λ p q, polynomial.map_add g,
  map_one' := polynomial.map_one g,
  map_mul' := λ p q, polynomial.map_mul g }

@[simp] theorem coe_polynomial (g : P →+*[M] Q) :
  (g.polynomial : polynomial P → polynomial Q) = map g :=
rfl

end mul_semiring_action_hom
