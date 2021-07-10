/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/

import data.polynomial.eval
import algebra.algebra.tower

/-!
# Theory of univariate polynomials

We show that `polynomial A` is an R-algebra when `A` is an R-algebra.
We promote `eval₂` to an algebra hom in `aeval`.
-/

noncomputable theory
open finset
open_locale big_operators

namespace polynomial
universes u v w z
variables {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

section comm_semiring
variables [comm_semiring R] {p q r : polynomial R}

variables [semiring A] [algebra R A]

/-- Note that this instance also provides `algebra R (polynomial R)`. -/
instance algebra_of_algebra : algebra R (polynomial A) :=
{ smul_def' := λ r p, begin
    rcases p,
    simp only [C, monomial, monomial_fun, ring_hom.coe_mk, ring_hom.to_fun_eq_coe,
      function.comp_app, ring_hom.coe_comp, smul_to_finsupp, mul_to_finsupp],
    exact algebra.smul_def' _ _,
  end,
  commutes' := λ r p, begin
    rcases p,
    simp only [C, monomial, monomial_fun, ring_hom.coe_mk, ring_hom.to_fun_eq_coe,
      function.comp_app, ring_hom.coe_comp, mul_to_finsupp],
    convert algebra.commutes' r p,
  end,
  .. C.comp (algebra_map R A) }

lemma algebra_map_apply (r : R) :
  algebra_map R (polynomial A) r = C (algebra_map R A r) :=
rfl

/--
When we have `[comm_ring R]`, the function `C` is the same as `algebra_map R (polynomial R)`.

(But note that `C` is defined when `R` is not necessarily commutative, in which case
`algebra_map` is not available.)
-/
lemma C_eq_algebra_map {R : Type*} [comm_semiring R] (r : R) :
  C r = algebra_map R (polynomial R) r :=
rfl

variable (R)

/-- Algebra isomorphism between `polynomial R` and `add_monoid_algebra R ℕ`. This is just an
implementation detail, but it can be useful to transfer results from `finsupp` to polynomials. -/
@[simps]
def to_finsupp_iso_alg : polynomial R ≃ₐ[R] add_monoid_algebra R ℕ :=
{ commutes' := λ r,
  begin
    simp only [add_monoid_algebra.coe_algebra_map, algebra.id.map_eq_self, function.comp_app],
    rw [←C_eq_algebra_map, ←monomial_zero_left, ring_equiv.to_fun_eq_coe, to_finsupp_iso_monomial],
  end,
  ..to_finsupp_iso R }

variable {R}

instance [nontrivial A] : nontrivial (subalgebra R (polynomial A)) :=
⟨⟨⊥, ⊤, begin
  rw [ne.def, set_like.ext_iff, not_forall],
  refine ⟨X, _⟩,
  simp only [algebra.mem_bot, not_exists, set.mem_range, iff_true, algebra.mem_top,
    algebra_map_apply, not_forall],
  intro x,
  rw [ext_iff, not_forall],
  refine ⟨1, _⟩,
  simp [coeff_C],
end⟩⟩

@[simp]
lemma alg_hom_eval₂_algebra_map
  {R A B : Type*} [comm_ring R] [ring A] [ring B] [algebra R A] [algebra R B]
  (p : polynomial R) (f : A →ₐ[R] B) (a : A) :
  f (eval₂ (algebra_map R A) a p) = eval₂ (algebra_map R B) (f a) p :=
begin
  dsimp [eval₂, sum],
  simp only [f.map_sum, f.map_mul, f.map_pow, ring_hom.eq_int_cast, ring_hom.map_int_cast,
    alg_hom.commutes],
end

@[simp]
lemma eval₂_algebra_map_X {R A : Type*} [comm_ring R] [ring A] [algebra R A]
  (p : polynomial R) (f : polynomial R →ₐ[R] A) :
  eval₂ (algebra_map R A) (f X) p = f p :=
begin
  conv_rhs { rw [←polynomial.sum_C_mul_X_eq p], },
  dsimp [eval₂, sum],
  simp only [f.map_sum, f.map_mul, f.map_pow, ring_hom.eq_int_cast, ring_hom.map_int_cast],
  simp [polynomial.C_eq_algebra_map],
end

@[simp]
lemma ring_hom_eval₂_algebra_map_int {R S : Type*} [ring R] [ring S]
  (p : polynomial ℤ) (f : R →+* S) (r : R) :
  f (eval₂ (algebra_map ℤ R) r p) = eval₂ (algebra_map ℤ S) (f r) p :=
alg_hom_eval₂_algebra_map p f.to_int_alg_hom r

@[simp]
lemma eval₂_algebra_map_int_X {R : Type*} [ring R] (p : polynomial ℤ) (f : polynomial ℤ →+* R) :
  eval₂ (algebra_map ℤ R) (f X) p = f p :=
-- Unfortunately `f.to_int_alg_hom` doesn't work here, as typeclasses don't match up correctly.
eval₂_algebra_map_X p { commutes' := λ n, by simp, .. f }

end comm_semiring

section aeval
variables [comm_semiring R] {p q : polynomial R}

variables [semiring A] [algebra R A]
variables {B : Type*} [semiring B] [algebra R B]
variables (x : A)

/-- Given a valuation `x` of the variable in an `R`-algebra `A`, `aeval R A x` is
the unique `R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`. -/
def aeval : polynomial R →ₐ[R] A :=
{ commutes' := λ r, eval₂_C _ _,
  ..eval₂_ring_hom' (algebra_map R A) x (λ a, algebra.commutes _ _) }

variables {R A}

@[ext] lemma alg_hom_ext {f g : polynomial R →ₐ[R] A} (h : f X = g X) : f = g :=
begin
  ext p,
  rw [← sum_monomial_eq p],
  simp [sum, f.map_sum, g.map_sum, monomial_eq_smul_X, h],
end

theorem aeval_def (p : polynomial R) : aeval x p = eval₂ (algebra_map R A) x p := rfl

@[simp] lemma aeval_zero : aeval x (0 : polynomial R) = 0 :=
alg_hom.map_zero (aeval x)

@[simp] lemma aeval_X : aeval x (X : polynomial R) = x := eval₂_X _ x

@[simp] lemma aeval_C (r : R) : aeval x (C r) = algebra_map R A r := eval₂_C _ x

@[simp] lemma aeval_monomial {n : ℕ} {r : R} : aeval x (monomial n r) = (algebra_map _ _ r) * x^n :=
eval₂_monomial _ _

@[simp] lemma aeval_X_pow {n : ℕ} : aeval x ((X : polynomial R)^n) = x^n :=
eval₂_X_pow _ _

@[simp] lemma aeval_add : aeval x (p + q) = aeval x p + aeval x q :=
alg_hom.map_add _ _ _

@[simp] lemma aeval_one : aeval x (1 : polynomial R) = 1 :=
alg_hom.map_one _

@[simp] lemma aeval_bit0 : aeval x (bit0 p) = bit0 (aeval x p) :=
alg_hom.map_bit0 _ _

@[simp] lemma aeval_bit1 : aeval x (bit1 p) = bit1 (aeval x p) :=
alg_hom.map_bit1 _ _

@[simp] lemma aeval_nat_cast (n : ℕ) : aeval x (n : polynomial R) = n :=
alg_hom.map_nat_cast _ _

lemma aeval_mul : aeval x (p * q) = aeval x p * aeval x q :=
alg_hom.map_mul _ _ _

lemma aeval_comp {A : Type*} [comm_semiring A] [algebra R A] (x : A) :
  aeval x (p.comp q) = (aeval (aeval x q) p) :=
eval₂_comp (algebra_map R A)

@[simp] lemma aeval_map {A : Type*} [comm_semiring A] [algebra R A] [algebra A B]
  [is_scalar_tower R A B] (b : B) (p : polynomial R) :
  aeval b (p.map (algebra_map R A)) = aeval b p :=
by rw [aeval_def, eval₂_map, ←is_scalar_tower.algebra_map_eq, ←aeval_def]

theorem eval_unique (φ : polynomial R →ₐ[R] A) (p) :
  φ p = eval₂ (algebra_map R A) (φ X) p :=
begin
  apply polynomial.induction_on p,
  { intro r, rw eval₂_C, exact φ.commutes r },
  { intros f g ih1 ih2,
    rw [φ.map_add, ih1, ih2, eval₂_add] },
  { intros n r ih,
    rw [pow_succ', ← mul_assoc, φ.map_mul,
        eval₂_mul_noncomm (algebra_map R A) _ (λ k, algebra.commutes _ _), eval₂_X, ih] }
end

theorem aeval_alg_hom (f : A →ₐ[R] B) (x : A) : aeval (f x) = f.comp (aeval x) :=
alg_hom.ext $ λ p, by rw [eval_unique (f.comp (aeval x)), alg_hom.comp_apply, aeval_X, aeval_def]

theorem aeval_alg_hom_apply (f : A →ₐ[R] B) (x : A) (p : polynomial R) :
  aeval (f x) p = f (aeval x p) :=
alg_hom.ext_iff.1 (aeval_alg_hom f x) p

theorem aeval_alg_equiv (f : A ≃ₐ[R] B) (x : A) : aeval (f x) = (f : A →ₐ[R] B).comp (aeval x) :=
aeval_alg_hom (f : A →ₐ[R] B) x

theorem aeval_alg_equiv_apply (f : A ≃ₐ[R] B) (x : A) (p : polynomial R) :
  aeval (f x) p = f (aeval x p) :=
aeval_alg_hom_apply (f : A →ₐ[R] B) x p

lemma aeval_algebra_map_apply (x : R) (p : polynomial R) :
  aeval (algebra_map R A x) p = algebra_map R A (p.eval x) :=
aeval_alg_hom_apply (algebra.of_id R A) x p

@[simp] lemma coe_aeval_eq_eval (r : R) :
  (aeval r : polynomial R → R) = eval r := rfl

@[simp] lemma aeval_fn_apply {X : Type*} (g : polynomial R) (f : X → R) (x : X) :
  ((aeval f) g) x = aeval (f x) g :=
(aeval_alg_hom_apply (pi.eval_alg_hom _ _ x) f g).symm

@[norm_cast] lemma aeval_subalgebra_coe
  (g : polynomial R) {A : Type*} [semiring A] [algebra R A] (s : subalgebra R A) (f : s) :
  (aeval f g : A) = aeval (f : A) g :=
(aeval_alg_hom_apply s.val f g).symm

lemma coeff_zero_eq_aeval_zero (p : polynomial R) : p.coeff 0 = aeval 0 p :=
by simp [coeff_zero_eq_eval_zero]

section comm_semiring

variables [comm_semiring S] {f : R →+* S}

lemma aeval_eq_sum_range [algebra R S] {p : polynomial R} (x : S) :
  aeval x p = ∑ i in finset.range (p.nat_degree + 1), p.coeff i • x ^ i :=
by { simp_rw algebra.smul_def, exact eval₂_eq_sum_range (algebra_map R S) x }

lemma aeval_eq_sum_range' [algebra R S] {p : polynomial R} {n : ℕ} (hn : p.nat_degree < n) (x : S) :
aeval x p = ∑ i in finset.range n, p.coeff i • x ^ i :=
by { simp_rw algebra.smul_def, exact eval₂_eq_sum_range' (algebra_map R S) hn x }

lemma is_root_of_eval₂_map_eq_zero
  (hf : function.injective f) {r : R} : eval₂ f (f r) p = 0 → p.is_root r :=
begin
  intro h,
  apply hf,
  rw [←eval₂_hom, h, f.map_zero],
end

lemma is_root_of_aeval_algebra_map_eq_zero [algebra R S] {p : polynomial R}
  (inj : function.injective (algebra_map R S))
  {r : R} (hr : aeval (algebra_map R S r) p = 0) : p.is_root r :=
is_root_of_eval₂_map_eq_zero inj hr

end comm_semiring

section comm_ring

variables [comm_ring S] {f : R →+* S}

lemma dvd_term_of_dvd_eval_of_dvd_terms {z p : S} {f : polynomial S} (i : ℕ)
  (dvd_eval : p ∣ f.eval z) (dvd_terms : ∀ (j ≠ i), p ∣ f.coeff j * z ^ j) :
  p ∣ f.coeff i * z ^ i :=
begin
  by_cases hf : f = 0,
  { simp [hf] },
  by_cases hi : i ∈ f.support,
  { rw [eval, eval₂, sum] at dvd_eval,
    rw [←finset.insert_erase hi, finset.sum_insert (finset.not_mem_erase _ _)] at dvd_eval,
    refine (dvd_add_left _).mp dvd_eval,
    apply finset.dvd_sum,
    intros j hj,
    exact dvd_terms j (finset.ne_of_mem_erase hj) },
  { convert dvd_zero p,
    rw not_mem_support_iff at hi,
    simp [hi] }
end

lemma dvd_term_of_is_root_of_dvd_terms {r p : S} {f : polynomial S} (i : ℕ)
  (hr : f.is_root r) (h : ∀ (j ≠ i), p ∣ f.coeff j * r ^ j) : p ∣ f.coeff i * r ^ i :=
dvd_term_of_dvd_eval_of_dvd_terms i (eq.symm hr ▸ dvd_zero p) h

end comm_ring

end aeval

section ring
variables [ring R]

/--
The evaluation map is not generally multiplicative when the coefficient ring is noncommutative,
but nevertheless any polynomial of the form `p * (X - monomial 0 r)` is sent to zero
when evaluated at `r`.

This is the key step in our proof of the Cayley-Hamilton theorem.
-/
lemma eval_mul_X_sub_C {p : polynomial R} (r : R) :
  (p * (X - C r)).eval r = 0 :=
begin
  simp only [eval, eval₂, ring_hom.id_apply],
  have bound := calc
    (p * (X - C r)).nat_degree
         ≤ p.nat_degree + (X - C r).nat_degree : nat_degree_mul_le
     ... ≤ p.nat_degree + 1 : add_le_add_left nat_degree_X_sub_C_le _
     ... < p.nat_degree + 2 : lt_add_one _,
  rw sum_over_range' _ _ (p.nat_degree + 2) bound,
  swap,
  { simp, },
  rw sum_range_succ',
  conv_lhs {
    congr, apply_congr, skip,
    rw [coeff_mul_X_sub_C, sub_mul, mul_assoc, ←pow_succ],
  },
  simp [sum_range_sub', coeff_monomial],
end

theorem not_is_unit_X_sub_C [nontrivial R] {r : R} : ¬ is_unit (X - C r) :=
λ ⟨⟨_, g, hfg, hgf⟩, rfl⟩, @zero_ne_one R _ _ $ by erw [← eval_mul_X_sub_C, hgf, eval_one]

end ring

lemma aeval_endomorphism {M : Type*}
  [comm_ring R] [add_comm_group M] [module R M]
  (f : M →ₗ[R] M) (v : M) (p : polynomial R) :
  aeval f p v = p.sum (λ n b, b • (f ^ n) v) :=
begin
  rw [aeval_def, eval₂],
  exact (finset.sum_hom p.support (λ h : M →ₗ[R] M, h v)).symm
end

end polynomial
