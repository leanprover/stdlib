/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/

import data.polynomial.eval
import data.finsupp.antidiagonal

/-!
# Multivariate polynomials

This file defines polynomial rings over a base ring (or even semiring),
with variables from a general type `σ` (which could be infinite).

## Important definitions

Let `R` be a commutative ring (or a semiring) and let `σ` be an arbitrary
type. This file creates the type `mv_polynomial σ R`, which mathematicians
might denote $R[X_i : i \in σ]$. It is the type of multivariate
(a.k.a. multivariable) polynomials, with variables
corresponding to the terms in `σ`, and coefficients in `R`.

### Notation

In the definitions below, we use the following notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_semiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

### Definitions

* `mv_polynomial σ R` : the type of polynomials with variables of type `σ` and coefficients
  in the commutative semiring `R`

* `monomial s a` : the monomial which mathematically would be denoted `a * X^s`

* `C a` : the constant polynomial with value `a`

* `X i` : the degree one monomial corresponding to i; mathematically this might be denoted `Xᵢ`.

* `coeff s p` : the coefficient of `s` in `p`.

* `eval₂ (f : R → S₁) (g : σ → S₁) p` : given a semiring homomorphism from `R` to another
  semiring `S₁`, and a map `σ → S₁`, evaluates `p` at this valuation, returning a term of type `S₁`.
  Note that `eval₂` can be made using `eval` and `map` (see below), and it has been suggested
  that sticking to `eval` and `map` might make the code less brittle.

* `eval (g : σ → R) p` : given a map `σ → R`, evaluates `p` at this valuation,
  returning a term of type `R`

* `map (f : R → S₁) p` : returns the multivariate polynomial obtained from `p` by the change of
  coefficient semiring corresponding to `f`

## Implementation notes

Recall that if `Y` has a zero, then `X →₀ Y` is the type of functions from `X` to `Y` with finite
support, i.e. such that only finitely many elements of `X` get sent to non-zero terms in `Y`.
The definition of `mv_polynomial σ R` is `(σ →₀ ℕ) →₀ R` ; here `σ →₀ ℕ` denotes the space of all
monomials in the variables, and the function to `R` sends a monomial to its coefficient in
the polynomial being represented.

## Tags

polynomial, multivariate polynomial, multivariable polynomial

-/

noncomputable theory

open_locale classical big_operators

open set function finsupp add_monoid_algebra
open_locale big_operators

universes u v w x
variables {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

/-- Multivariate polynomial, where `σ` is the index set of the variables and
  `R` is the coefficient ring -/
def mv_polynomial (σ : Type*) (R : Type*) [comm_semiring R] := add_monoid_algebra R (σ →₀ ℕ)

namespace mv_polynomial
variables {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section comm_semiring

section instances

instance decidable_eq_mv_polynomial [comm_semiring R] [decidable_eq σ] [decidable_eq R] :
  decidable_eq (mv_polynomial σ R) := finsupp.decidable_eq
instance [comm_semiring R] : comm_semiring (mv_polynomial σ R) := add_monoid_algebra.comm_semiring
instance [comm_semiring R] : inhabited (mv_polynomial σ R) := ⟨0⟩
instance [monoid R] [comm_semiring S₁] [distrib_mul_action R S₁] :
  distrib_mul_action R (mv_polynomial σ S₁) :=
add_monoid_algebra.distrib_mul_action
instance [semiring R] [comm_semiring S₁] [module R S₁] : module R (mv_polynomial σ S₁) :=
add_monoid_algebra.module
instance [monoid R] [monoid S₁] [comm_semiring S₂]
  [has_scalar R S₁] [distrib_mul_action R S₂] [distrib_mul_action S₁ S₂] [is_scalar_tower R S₁ S₂] :
  is_scalar_tower R S₁ (mv_polynomial σ S₂) :=
add_monoid_algebra.is_scalar_tower
instance [monoid R] [monoid S₁][comm_semiring S₂]
  [distrib_mul_action R S₂] [distrib_mul_action S₁ S₂] [smul_comm_class R S₁ S₂] :
  smul_comm_class R S₁ (mv_polynomial σ S₂) :=
add_monoid_algebra.smul_comm_class
instance [comm_semiring R] [comm_semiring S₁] [algebra R S₁] : algebra R (mv_polynomial σ S₁) :=
add_monoid_algebra.algebra

end instances

variables [comm_semiring R] [comm_semiring S₁] {p q : mv_polynomial σ R}

/-- `monomial s a` is the monomial with coefficient `a` and exponents given by `s`  -/
def monomial (s : σ →₀ ℕ) (a : R) : mv_polynomial σ R := single s a

lemma single_eq_monomial (s : σ →₀ ℕ) (a : R) : single s a = monomial s a := rfl

lemma mul_def : (p * q) = p.sum (λ m a, q.sum $ λ n b, monomial (m + n) (a * b)) := rfl

/-- `C a` is the constant polynomial with value `a` -/
def C : R →+* mv_polynomial σ R :=
{ to_fun := monomial 0, ..single_zero_ring_hom }

variables (R σ)
theorem algebra_map_eq : algebra_map R (mv_polynomial σ R) = C := rfl
variables {R σ}

/-- `X n` is the degree `1` monomial $X_n$. -/
def X (n : σ) : mv_polynomial σ R := monomial (single n 1) 1

lemma C_apply : (C a : mv_polynomial σ R) = monomial 0 a := rfl

@[simp] lemma C_0 : C 0 = (0 : mv_polynomial σ R) := by simp [C_apply, monomial]

@[simp] lemma C_1 : C 1 = (1 : mv_polynomial σ R) := rfl

lemma C_mul_monomial : C a * monomial s a' = monomial s (a * a') :=
by simp [C_apply, monomial, single_mul_single]

@[simp] lemma C_add : (C (a + a') : mv_polynomial σ R) = C a + C a' := single_add

@[simp] lemma C_mul : (C (a * a') : mv_polynomial σ R) = C a * C a' := C_mul_monomial.symm

@[simp] lemma C_pow (a : R) (n : ℕ) : (C (a^n) : mv_polynomial σ R) = (C a)^n :=
by induction n; simp [pow_succ, *]

lemma C_injective (σ : Type*) (R : Type*) [comm_semiring R] :
  function.injective (C : R → mv_polynomial σ R) :=
finsupp.single_injective _

lemma C_surjective {R : Type*} [comm_semiring R] (σ : Type*) (hσ : ¬ nonempty σ) :
  function.surjective (C : R → mv_polynomial σ R) :=
begin
  refine λ p, ⟨p.to_fun 0, finsupp.ext (λ a, _)⟩,
  simpa [(finsupp.ext (λ x, absurd (nonempty.intro x) hσ) : a = 0), C_apply, monomial],
end

lemma C_surjective_fin_0 {R : Type*} [comm_ring R] :
  function.surjective (mv_polynomial.C : R → mv_polynomial (fin 0) R) :=
C_surjective (fin 0) (λ h, let ⟨n⟩ := h in fin_zero_elim n)

@[simp] lemma C_inj {σ : Type*} (R : Type*) [comm_semiring R] (r s : R) :
  (C r : mv_polynomial σ R) = C s ↔ r = s :=
(C_injective σ R).eq_iff

instance infinite_of_infinite (σ : Type*) (R : Type*) [comm_semiring R] [infinite R] :
  infinite (mv_polynomial σ R) :=
infinite.of_injective C (C_injective _ _)

instance infinite_of_nonempty (σ : Type*) (R : Type*) [nonempty σ] [comm_semiring R]
  [nontrivial R] :
  infinite (mv_polynomial σ R) :=
infinite.of_injective ((λ s : σ →₀ ℕ, monomial s 1) ∘ single (classical.arbitrary σ)) $
  function.injective.comp
    (λ m n, (finsupp.single_left_inj one_ne_zero).mp) (finsupp.single_injective _)

lemma C_eq_coe_nat (n : ℕ) : (C ↑n : mv_polynomial σ R) = n :=
by induction n; simp [nat.succ_eq_add_one, *]

theorem C_mul' : mv_polynomial.C a * p = a • p :=
(algebra.smul_def a p).symm

lemma smul_eq_C_mul (p : mv_polynomial σ R) (a : R) : a • p = C a * p := C_mul'.symm

lemma X_pow_eq_single : X n ^ e = monomial (single n e) (1 : R) :=
begin
  induction e,
  { simp [X], refl },
  { simp [pow_succ, e_ih],
    simp [X, monomial, single_mul_single, nat.succ_eq_add_one, add_comm] }
end

lemma monomial_add_single : monomial (s + single n e) a = (monomial s a * X n ^ e) :=
by rw [X_pow_eq_single, monomial, monomial, monomial, single_mul_single]; simp

lemma monomial_single_add : monomial (single n e + s) a = (X n ^ e * monomial s a) :=
by rw [X_pow_eq_single, monomial, monomial, monomial, single_mul_single]; simp

lemma monomial_eq_C_mul_X {s : σ} {a : R} {n : ℕ} :
  monomial (single s n) a = C a * (X s)^n :=
by rw [← zero_add (single s n), monomial_add_single, C_apply]

@[simp] lemma monomial_add {s : σ →₀ ℕ} {a b : R} :
  monomial s a + monomial s b = monomial s (a + b) :=
single_add.symm

@[simp] lemma monomial_mul {s s' : σ →₀ ℕ} {a b : R} :
  monomial s a * monomial s' b = monomial (s + s') (a * b) :=
add_monoid_algebra.single_mul_single

@[simp] lemma monomial_zero {s : σ →₀ ℕ}: monomial s (0 : R) = 0 :=
single_zero

@[simp] lemma sum_monomial_eq  {A : Type*} [add_comm_monoid A]
  {u : σ →₀ ℕ} {r : R} {b : (σ →₀ ℕ) → R → A} (w : b u 0 = 0) :
  sum (monomial u r) b = b u r :=
sum_single_index w

@[simp] lemma sum_C {A : Type*} [add_comm_monoid A]
  {b : (σ →₀ ℕ) → R → A} (w : b 0 0 = 0) :
  sum (C a) b = b 0 a :=
by simp [C_apply, w]

lemma monomial_eq : monomial s a = C a * (s.prod $ λn e, X n ^ e : mv_polynomial σ R) :=
begin
  apply @finsupp.induction σ ℕ _ _ s,
  { simp only [C_apply, prod_zero_index]; exact (mul_one _).symm },
  { assume n e s hns he ih,
    rw [monomial_single_add, ih, prod_add_index, prod_single_index, mul_left_comm],
    { simp only [pow_zero], },
    { intro a, simp only [pow_zero], },
    { intros, rw pow_add, }, }
end

@[recursor 5]
lemma induction_on {M : mv_polynomial σ R → Prop} (p : mv_polynomial σ R)
  (h_C : ∀a, M (C a)) (h_add : ∀p q, M p → M q → M (p + q)) (h_X : ∀p n, M p → M (p * X n)) :
  M p :=
have ∀s a, M (monomial s a),
begin
  assume s a,
  apply @finsupp.induction σ ℕ _ _ s,
  { show M (monomial 0 a), from h_C a, },
  { assume n e p hpn he ih,
    have : ∀e:ℕ, M (monomial p a * X n ^ e),
    { intro e,
      induction e,
      { simp [ih] },
      { simp [ih, pow_succ', (mul_assoc _ _ _).symm, h_X, e_ih] } },
    simp [add_comm, monomial_add_single, this] }
end,
finsupp.induction p
  (by have : M (C 0) := h_C 0; rwa [C_0] at this)
  (assume s a p hsp ha hp, h_add _ _ (this s a) hp)

attribute [elab_as_eliminator]
theorem induction_on' {P : mv_polynomial σ R → Prop} (p : mv_polynomial σ R)
    (h1 : ∀ (u : σ →₀ ℕ) (a : R), P (monomial u a))
    (h2 : ∀ (p q : mv_polynomial σ R), P p → P q → P (p + q)) : P p :=
finsupp.induction p (suffices P (monomial 0 0), by rwa monomial_zero at this,
                     show P (monomial 0 0), from h1 0 0)
                    (λ a b f ha hb hPf, h2 _ _ (h1 _ _) hPf)


@[ext] lemma ring_hom_ext {A : Type*} [semiring A] {f g : mv_polynomial σ R →+* A}
  (hC : ∀ r, f (C r) = g (C r)) (hX : ∀ i, f (X i) = g (X i)) :
  f = g :=
by { ext, exacts [hC _, hX _] }

lemma hom_eq_hom [semiring S₂]
  (f g : mv_polynomial σ R →+* S₂)
  (hC : ∀a:R, f (C a) = g (C a)) (hX : ∀n:σ, f (X n) = g (X n)) (p : mv_polynomial σ R) :
  f p = g p :=
ring_hom.congr_fun (ring_hom_ext hC hX) p

lemma is_id (f : mv_polynomial σ R →+* mv_polynomial σ R)
  (hC : ∀a:R, f (C a) = (C a)) (hX : ∀n:σ, f (X n) = (X n)) (p : mv_polynomial σ R) :
  f p = p :=
hom_eq_hom f (ring_hom.id _) hC hX p

@[ext] lemma alg_hom_ext {A : Type*} [comm_semiring A] [algebra R A]
  {f g : mv_polynomial σ R →ₐ[R] A} (hf : ∀ i : σ, f (X i) = g (X i)) :
  f = g :=
by { ext, exact hf _ }

@[simp] lemma alg_hom_C (f : mv_polynomial σ R →ₐ[R] mv_polynomial σ R) (r : R) :
  f (C r) = C r :=
f.commutes r


section support

/--
The finite set of all `m : σ →₀ ℕ` such that `X^m` has a non-zero coefficient.
-/
def support (p : mv_polynomial σ R) : finset (σ →₀ ℕ) :=
p.support

lemma support_monomial [decidable (a = 0)] : (monomial s a).support = if a = 0 then ∅ else {s} :=
by convert rfl

lemma support_monomial_subset : (monomial s a).support ⊆ {s} :=
support_single_subset

lemma support_add : (p + q).support ⊆ p.support ∪ q.support := finsupp.support_add

lemma support_X [nontrivial R] : (X n : mv_polynomial σ R).support = {single n 1} :=
by rw [X, support_monomial, if_neg]; exact one_ne_zero

end support

section coeff

/-- The coefficient of the monomial `m` in the multi-variable polynomial `p`. -/
def coeff (m : σ →₀ ℕ) (p : mv_polynomial σ R) : R :=
@coe_fn _ (monoid_algebra.has_coe_to_fun _ _) p m

@[simp] lemma mem_support_iff {p : mv_polynomial σ R} {m : σ →₀ ℕ} :
  m ∈ p.support ↔ p.coeff m ≠ 0 :=
by simp [support, coeff]

lemma not_mem_support_iff {p : mv_polynomial σ R} {m : σ →₀ ℕ} :
  m ∉ p.support ↔ p.coeff m = 0 :=
by simp

lemma sum_def {A} [add_comm_monoid A] {p : mv_polynomial σ R} {b : (σ →₀ ℕ) → R → A} :
  p.sum b = ∑ m in p.support, b m (p.coeff m) :=
by simp [support, finsupp.sum, coeff]

lemma support_mul (p q : mv_polynomial σ R) :
  (p * q).support ⊆ p.support.bUnion (λ a, q.support.bUnion $ λ b, {a + b}) :=
by convert add_monoid_algebra.support_mul p q; ext; convert iff.rfl

@[ext] lemma ext (p q : mv_polynomial σ R) :
  (∀ m, coeff m p = coeff m q) → p = q := ext

lemma ext_iff (p q : mv_polynomial σ R) :
  p = q ↔ (∀ m, coeff m p = coeff m q) :=
⟨ λ h m, by rw h, ext p q⟩

@[simp] lemma coeff_add (m : σ →₀ ℕ) (p q : mv_polynomial σ R) :
  coeff m (p + q) = coeff m p + coeff m q := add_apply p q m

@[simp] lemma coeff_smul {S₁ : Type*} [monoid S₁] [distrib_mul_action S₁ R]
  (m : σ →₀ ℕ) (c : S₁) (p : mv_polynomial σ R) :
  coeff m (c • p) = c • coeff m p := smul_apply c p m

@[simp] lemma coeff_zero (m : σ →₀ ℕ) :
  coeff m (0 : mv_polynomial σ R) = 0 := rfl

@[simp] lemma coeff_zero_X (i : σ) : coeff 0 (X i : mv_polynomial σ R) = 0 :=
single_eq_of_ne (λ h, by cases single_eq_zero.1 h)

instance coeff.is_add_monoid_hom (m : σ →₀ ℕ) :
  is_add_monoid_hom (coeff m : mv_polynomial σ R → R) :=
{ map_add := coeff_add m,
  map_zero := coeff_zero m }

lemma coeff_sum {X : Type*} (s : finset X) (f : X → mv_polynomial σ R) (m : σ →₀ ℕ) :
  coeff m (∑ x in s, f x) = ∑ x in s, coeff m (f x) :=
(s.sum_hom _).symm

lemma monic_monomial_eq (m) : monomial m (1:R) = (m.prod $ λn e, X n ^ e : mv_polynomial σ R) :=
by simp [monomial_eq]

@[simp] lemma coeff_monomial [decidable_eq σ] (m n) (a) :
  coeff m (monomial n a : mv_polynomial σ R) = if n = m then a else 0 :=
single_apply

@[simp] lemma coeff_C [decidable_eq σ] (m) (a) :
  coeff m (C a : mv_polynomial σ R) = if 0 = m then a else 0 :=
single_apply

lemma coeff_one [decidable_eq σ] (m) :
  coeff m (1 : mv_polynomial σ R) = if 0 = m then 1 else 0 :=
coeff_C m 1

@[simp] lemma coeff_zero_C (a) : coeff 0 (C a : mv_polynomial σ R) = a :=
single_eq_same

@[simp] lemma coeff_zero_one : coeff 0 (1 : mv_polynomial σ R) = 1 :=
coeff_zero_C 1

lemma coeff_X_pow [decidable_eq σ] (i : σ) (m) (k : ℕ) :
  coeff m (X i ^ k : mv_polynomial σ R) = if single i k = m then 1 else 0 :=
begin
  have := coeff_monomial m (finsupp.single i k) (1:R),
  rwa [@monomial_eq _ _ (1:R) (finsupp.single i k) _,
    C_1, one_mul, finsupp.prod_single_index] at this,
  exact pow_zero _
end

lemma coeff_X' [decidable_eq σ] (i : σ) (m) :
  coeff m (X i : mv_polynomial σ R) = if single i 1 = m then 1 else 0 :=
by rw [← coeff_X_pow, pow_one]

@[simp] lemma coeff_X (i : σ) :
  coeff (single i 1) (X i : mv_polynomial σ R) = 1 :=
by rw [coeff_X', if_pos rfl]

@[simp] lemma coeff_C_mul (m) (a : R) (p : mv_polynomial σ R) :
  coeff m (C a * p) = a * coeff m p :=
begin
  rw [mul_def, sum_C],
  { simp [sum_def, coeff_sum] {contextual := tt} },
  simp
end

lemma coeff_mul (p q : mv_polynomial σ R) (n : σ →₀ ℕ) :
  coeff n (p * q) = ∑ x in antidiagonal n, coeff x.1 p * coeff x.2 q :=
begin
  rw mul_def,
  -- We need to manipulate both sides into a shape to which we can apply `finset.sum_bij_ne_zero`,
  -- so we need to turn both sides into a sum over a product.
  have := @finset.sum_product R (σ →₀ ℕ) _ _ p.support q.support
    (λ x, if (x.1 + x.2 = n) then coeff x.1 p * coeff x.2 q else 0),
  convert this.symm using 1; clear this,
  { rw [coeff],
    iterate 2 { rw sum_apply, apply finset.sum_congr rfl, intros, dsimp only },
    exact single_apply },
  symmetry,
  -- We are now ready to show that both sums are equal using `finset.sum_bij_ne_zero`.
  apply finset.sum_bij_ne_zero (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)) _ _, (x.1, x.2)),
  { intros x hx hx',
    simp only [mem_antidiagonal, eq_self_iff_true, if_false, forall_true_iff],
    contrapose! hx',
    rw [if_neg hx'] },
  { rintros ⟨i, j⟩ ⟨k, l⟩ hij hij' hkl hkl',
    simpa only [and_imp, prod.mk.inj_iff, heq_iff_eq] using and.intro },
  { rintros ⟨i, j⟩ hij hij',
    refine ⟨⟨i, j⟩, _, _⟩,
    { simp only [mem_support_iff, finset.mem_product],
      contrapose! hij',
      exact mul_eq_zero_of_ne_zero_imp_eq_zero hij' },
    { rw [mem_antidiagonal] at hij,
      simp only [exists_prop, true_and, ne.def, if_pos hij, hij', not_false_iff] } },
  { intros x hx hx',
    simp only [ne.def] at hx' ⊢,
    split_ifs with H,
    { refl },
    { rw if_neg H at hx', contradiction } }
end

@[simp] lemma coeff_mul_X (m) (s : σ) (p : mv_polynomial σ R) :
  coeff (m + single s 1) (p * X s) = coeff m p :=
begin
  have : (m, single s 1) ∈ (m + single s 1).antidiagonal := mem_antidiagonal.2 rfl,
  rw [coeff_mul, ← finset.insert_erase this, finset.sum_insert (finset.not_mem_erase _ _),
      finset.sum_eq_zero, add_zero, coeff_X, mul_one],
  rintros ⟨i,j⟩ hij,
  rw [finset.mem_erase, mem_antidiagonal] at hij,
  by_cases H : single s 1 = j,
  { subst j, simpa using hij },
  { rw [coeff_X', if_neg H, mul_zero] },
end

lemma coeff_mul_X' [decidable_eq σ] (m) (s : σ) (p : mv_polynomial σ R) :
  coeff m (p * X s) = if s ∈ m.support then coeff (m - single s 1) p else 0 :=
begin
  nontriviality R,
  split_ifs with h h,
  { conv_rhs {rw ← coeff_mul_X _ s},
    congr' with  t,
    by_cases hj : s = t,
    { subst t, simp only [nat_sub_apply, add_apply, single_eq_same],
      refine (nat.sub_add_cancel $ nat.pos_of_ne_zero _).symm, rwa finsupp.mem_support_iff at h },
    { simp [single_eq_of_ne hj] } },
  { rw ← not_mem_support_iff, intro hm, apply h,
    have H := support_mul _ _ hm, simp only [finset.mem_bUnion] at H,
    rcases H with ⟨j, hj, i', hi', H⟩,
    rw [support_X, finset.mem_singleton] at hi', subst i',
    rw finset.mem_singleton at H, subst m,
    rw [finsupp.mem_support_iff, add_apply, single_apply, if_pos rfl],
    intro H, rw [_root_.add_eq_zero_iff] at H, exact one_ne_zero H.2 }
end

lemma eq_zero_iff {p : mv_polynomial σ R} :
  p = 0 ↔ ∀ d, coeff d p = 0 :=
by { rw ext_iff, simp only [coeff_zero], }

lemma ne_zero_iff {p : mv_polynomial σ R} :
  p ≠ 0 ↔ ∃ d, coeff d p ≠ 0 :=
by { rw [ne.def, eq_zero_iff], push_neg, }

lemma exists_coeff_ne_zero {p : mv_polynomial σ R} (h : p ≠ 0) :
  ∃ d, coeff d p ≠ 0 :=
ne_zero_iff.mp h

lemma C_dvd_iff_dvd_coeff (r : R) (φ : mv_polynomial σ R) :
  C r ∣ φ ↔ ∀ i, r ∣ φ.coeff i :=
begin
  split,
  { rintros ⟨φ, rfl⟩ c, rw coeff_C_mul, apply dvd_mul_right },
  { intro h,
    choose c hc using h,
    classical,
    let c' : (σ →₀ ℕ) → R := λ i, if i ∈ φ.support then c i else 0,
    let ψ : mv_polynomial σ R := ∑ i in φ.support, monomial i (c' i),
    use ψ,
    apply mv_polynomial.ext, intro i,
    simp only [coeff_C_mul, coeff_sum, coeff_monomial, finset.sum_ite_eq', c'],
    split_ifs with hi hi,
    { rw hc },
    { rw not_mem_support_iff at hi, rwa mul_zero } },
end

end coeff

section constant_coeff

/--
`constant_coeff p` returns the constant term of the polynomial `p`, defined as `coeff 0 p`.
This is a ring homomorphism.
-/
def constant_coeff : mv_polynomial σ R →+* R :=
{ to_fun := coeff 0,
  map_one' := by simp [coeff, add_monoid_algebra.one_def],
  map_mul' := by simp [coeff_mul, finsupp.support_single_ne_zero],
  map_zero' := coeff_zero _,
  map_add' := coeff_add _ }

lemma constant_coeff_eq : (constant_coeff : mv_polynomial σ R → R) = coeff 0 := rfl

@[simp]
lemma constant_coeff_C (r : R) :
  constant_coeff (C r : mv_polynomial σ R) = r :=
by simp [constant_coeff_eq]

@[simp]
lemma constant_coeff_X (i : σ) :
  constant_coeff (X i : mv_polynomial σ R) = 0 :=
by simp [constant_coeff_eq]

lemma constant_coeff_monomial [decidable_eq σ] (d : σ →₀ ℕ) (r : R) :
  constant_coeff (monomial d r) = if d = 0 then r else 0 :=
by rw [constant_coeff_eq, coeff_monomial]

variables (σ R)

@[simp] lemma constant_coeff_comp_C :
  constant_coeff.comp (C : R →+* mv_polynomial σ R) = ring_hom.id R :=
by { ext, apply constant_coeff_C }

@[simp] lemma constant_coeff_comp_algebra_map :
  constant_coeff.comp (algebra_map R (mv_polynomial σ R)) = ring_hom.id R :=
constant_coeff_comp_C _ _

end constant_coeff

section as_sum

@[simp] lemma support_sum_monomial_coeff (p : mv_polynomial σ R) :
  ∑ v in p.support, monomial v (coeff v p) = p :=
finsupp.sum_single p

lemma as_sum (p : mv_polynomial σ R) : p = ∑ v in p.support, monomial v (coeff v p) :=
(support_sum_monomial_coeff p).symm

end as_sum


section eval₂
variables (f : R →+* S₁) (g : σ → S₁)

/-- Evaluate a polynomial `p` given a valuation `g` of all the variables
  and a ring hom `f` from the scalar ring to the target -/
def eval₂ (p : mv_polynomial σ R) : S₁ :=
p.sum (λs a, f a * s.prod (λn e, g n ^ e))

lemma eval₂_eq (g : R →+* S₁) (x : σ → S₁) (f : mv_polynomial σ R) :
  f.eval₂ g x = ∑ d in f.support, g (f.coeff d) * ∏ i in d.support, x i ^ d i :=
rfl

lemma eval₂_eq' [fintype σ] (g : R →+* S₁) (x : σ → S₁) (f : mv_polynomial σ R) :
  f.eval₂ g x = ∑ d in f.support, g (f.coeff d) * ∏ i, x i ^ d i :=
by { simp only [eval₂_eq, ← finsupp.prod_pow], refl }

@[simp] lemma eval₂_zero : (0 : mv_polynomial σ R).eval₂ f g = 0 :=
finsupp.sum_zero_index

section

@[simp] lemma eval₂_add : (p + q).eval₂ f g = p.eval₂ f g + q.eval₂ f g :=
finsupp.sum_add_index
  (by simp [is_semiring_hom.map_zero f])
  (by simp [add_mul, is_semiring_hom.map_add f])

@[simp] lemma eval₂_monomial : (monomial s a).eval₂ f g = f a * s.prod (λn e, g n ^ e) :=
finsupp.sum_single_index (by simp [is_semiring_hom.map_zero f])

@[simp] lemma eval₂_C (a) : (C a).eval₂ f g = f a :=
by simp [eval₂_monomial, C, prod_zero_index]

@[simp] lemma eval₂_one : (1 : mv_polynomial σ R).eval₂ f g = 1 :=
(eval₂_C _ _ _).trans (is_semiring_hom.map_one f)

@[simp] lemma eval₂_X (n) : (X n).eval₂ f g = g n :=
by simp [eval₂_monomial,
  is_semiring_hom.map_one f, X, prod_single_index, pow_one]

lemma eval₂_mul_monomial :
  ∀{s a}, (p * monomial s a).eval₂ f g = p.eval₂ f g * f a * s.prod (λn e, g n ^ e) :=
begin
  apply mv_polynomial.induction_on p,
  { assume a' s a,
    simp [C_mul_monomial, eval₂_monomial, is_semiring_hom.map_mul f] },
  { assume p q ih_p ih_q, simp [add_mul, eval₂_add, ih_p, ih_q] },
  { assume p n ih s a,
    from calc (p * X n * monomial s a).eval₂ f g = (p * monomial (single n 1 + s) a).eval₂ f g :
        by simp [monomial_single_add, -add_comm, pow_one, mul_assoc]
      ... = (p * monomial (single n 1) 1).eval₂ f g * f a * s.prod (λn e, g n ^ e) :
        by simp [ih, prod_single_index, prod_add_index, pow_one, pow_add, mul_assoc, mul_left_comm,
          is_semiring_hom.map_one f, -add_comm] }
end

@[simp] lemma eval₂_mul : ∀{p}, (p * q).eval₂ f g = p.eval₂ f g * q.eval₂ f g :=
begin
  apply mv_polynomial.induction_on q,
  { simp [C, eval₂_monomial, eval₂_mul_monomial, prod_zero_index] },
  { simp [mul_add, eval₂_add] {contextual := tt} },
  { simp [X, eval₂_monomial, eval₂_mul_monomial, (mul_assoc _ _ _).symm] { contextual := tt} }
end

@[simp] lemma eval₂_pow {p:mv_polynomial σ R} : ∀{n:ℕ}, (p ^ n).eval₂ f g = (p.eval₂ f g)^n
| 0       := by { rw [pow_zero, pow_zero], exact eval₂_one _ _ }
| (n + 1) := by rw [pow_add, pow_one, pow_add, pow_one, eval₂_mul, eval₂_pow]

instance eval₂.is_semiring_hom : is_semiring_hom (eval₂ f g) :=
{ map_zero := eval₂_zero _ _,
  map_one := eval₂_one _ _,
  map_add := λ p q, eval₂_add _ _,
  map_mul := λ p q, eval₂_mul _ _ }

/-- `mv_polynomial.eval₂` as a `ring_hom`. -/
def eval₂_hom (f : R →+* S₁) (g : σ → S₁) : mv_polynomial σ R →+* S₁ := ring_hom.of (eval₂ f g)

@[simp] lemma coe_eval₂_hom (f : R →+* S₁) (g : σ → S₁) : ⇑(eval₂_hom f g) = eval₂ f g := rfl

lemma eval₂_hom_congr  {f₁ f₂ : R →+* S₁} {g₁ g₂ : σ → S₁} {p₁ p₂ : mv_polynomial σ R} :
  f₁ = f₂ → g₁ = g₂ → p₁ = p₂ →  eval₂_hom f₁ g₁ p₁ = eval₂_hom f₂ g₂ p₂ :=
by rintros rfl rfl rfl; refl
end

@[simp] lemma eval₂_hom_C (f : R →+* S₁) (g : σ → S₁) (r : R) :
  eval₂_hom f g (C r) = f r := eval₂_C f g r

@[simp] lemma eval₂_hom_X' (f : R →+* S₁) (g : σ → S₁) (i : σ) :
  eval₂_hom f g (X i) = g i := eval₂_X f g i

@[simp] lemma comp_eval₂_hom [comm_semiring S₂] (f : R →+* S₁) (g : σ → S₁) (φ : S₁ →+* S₂) :
  φ.comp (eval₂_hom f g) = (eval₂_hom (φ.comp f) (λ i, φ (g i))) :=
begin
  apply mv_polynomial.ring_hom_ext,
  { intro r, rw [ring_hom.comp_apply, eval₂_hom_C, eval₂_hom_C, ring_hom.comp_apply] },
  { intro i, rw [ring_hom.comp_apply, eval₂_hom_X', eval₂_hom_X'] }
end

lemma map_eval₂_hom  [comm_semiring S₂] (f : R →+* S₁) (g : σ → S₁) (φ : S₁ →+* S₂)
  (p : mv_polynomial σ R) :
  φ (eval₂_hom f g p) = (eval₂_hom (φ.comp f) (λ i, φ (g i)) p) :=
by { rw ← comp_eval₂_hom, refl }

lemma eval₂_hom_monomial (f : R →+* S₁) (g : σ → S₁) (d : σ →₀ ℕ) (r : R) :
  eval₂_hom f g (monomial d r) = f r * d.prod (λ i k, g i ^ k) :=
by simp only [monomial_eq, ring_hom.map_mul, eval₂_hom_C, finsupp.prod,
  ring_hom.map_prod, ring_hom.map_pow, eval₂_hom_X']

section
local attribute [instance, priority 10] is_semiring_hom.comp
lemma eval₂_comp_left {S₂} [comm_semiring S₂]
  (k : S₁ →+* S₂) (f : R →+* S₁) (g : σ → S₁)
  (p) : k (eval₂ f g p) = eval₂ (k.comp f) (k ∘ g) p :=
by apply mv_polynomial.induction_on p; simp [
  eval₂_add, k.map_add,
  eval₂_mul, k.map_mul] {contextual := tt}
end

@[simp] lemma eval₂_eta (p : mv_polynomial σ R) : eval₂ C X p = p :=
by apply mv_polynomial.induction_on p;
   simp [eval₂_add, eval₂_mul] {contextual := tt}

lemma eval₂_congr (g₁ g₂ : σ → S₁)
  (h : ∀ {i : σ} {c : σ →₀ ℕ}, i ∈ c.support → coeff c p ≠ 0 → g₁ i = g₂ i) :
  p.eval₂ f g₁ = p.eval₂ f g₂ :=
begin
  apply finset.sum_congr rfl,
  intros c hc, dsimp, congr' 1,
  apply finset.prod_congr rfl,
  intros i hi, dsimp, congr' 1,
  apply h hi,
  rwa finsupp.mem_support_iff at hc
end

@[simp] lemma eval₂_prod (s : finset S₂) (p : S₂ → mv_polynomial σ R) :
  eval₂ f g (∏ x in s, p x) = ∏ x in s, eval₂ f g (p x) :=
(s.prod_hom _).symm

@[simp] lemma eval₂_sum (s : finset S₂) (p : S₂ → mv_polynomial σ R) :
  eval₂ f g (∑ x in s, p x) = ∑ x in s, eval₂ f g (p x) :=
(s.sum_hom _).symm

attribute [to_additive] eval₂_prod

lemma eval₂_assoc (q : S₂ → mv_polynomial σ R) (p : mv_polynomial S₂ R) :
  eval₂ f (λ t, eval₂ f g (q t)) p = eval₂ f g (eval₂ C q p) :=
begin
  show _ = eval₂_hom f g (eval₂ C q p),
  rw eval₂_comp_left (eval₂_hom f g), congr' with a, simp,
end

end eval₂

section eval
variables {f : σ → R}

/-- Evaluate a polynomial `p` given a valuation `f` of all the variables -/
def eval (f : σ → R) : mv_polynomial σ R →+* R := eval₂_hom (ring_hom.id _) f

lemma eval_eq (x : σ → R) (f : mv_polynomial σ R) :
  eval x f = ∑ d in f.support, f.coeff d * ∏ i in d.support, x i ^ d i :=
rfl

lemma eval_eq' [fintype σ] (x : σ → R) (f : mv_polynomial σ R) :
  eval x f = ∑ d in f.support, f.coeff d * ∏ i, x i ^ d i :=
eval₂_eq' (ring_hom.id R) x f

lemma eval_monomial : eval f (monomial s a) = a * s.prod (λn e, f n ^ e) :=
eval₂_monomial _ _

@[simp] lemma eval_C : ∀ a, eval f (C a) = a := eval₂_C _ _

@[simp] lemma eval_X : ∀ n, eval f (X n) = f n := eval₂_X _ _

@[simp] lemma smul_eval (x) (p : mv_polynomial σ R) (s) : eval x (s • p) = s * eval x p :=
by rw [smul_eq_C_mul, (eval x).map_mul, eval_C]

lemma eval_sum {ι : Type*} (s : finset ι) (f : ι → mv_polynomial σ R) (g : σ → R) :
  eval g (∑ i in s, f i) = ∑ i in s, eval g (f i) :=
(eval g).map_sum _ _

@[to_additive]
lemma eval_prod {ι : Type*} (s : finset ι) (f : ι → mv_polynomial σ R) (g : σ → R) :
  eval g (∏ i in s, f i) = ∏ i in s, eval g (f i) :=
(eval g).map_prod _ _

theorem eval_assoc {τ}
  (f : σ → mv_polynomial τ R) (g : τ → R)
  (p : mv_polynomial σ R) :
  eval (eval g ∘ f) p = eval g (eval₂ C f p) :=
begin
  rw eval₂_comp_left (eval g),
  unfold eval, simp only [coe_eval₂_hom],
  congr' with a, simp
end

end eval

section map
variables (f : R →+* S₁)

/-- `map f p` maps a polynomial `p` across a ring hom `f` -/
def map : mv_polynomial σ R →+* mv_polynomial σ S₁ := eval₂_hom (C.comp f) X

@[simp] theorem map_monomial (s : σ →₀ ℕ) (a : R) : map f (monomial s a) = monomial s (f a) :=
(eval₂_monomial _ _).trans monomial_eq.symm

@[simp] theorem map_C : ∀ (a : R), map f (C a : mv_polynomial σ R) = C (f a) := map_monomial _ _

@[simp] theorem map_X : ∀ (n : σ), map f (X n : mv_polynomial σ R) = X n := eval₂_X _ _

theorem map_id : ∀ (p : mv_polynomial σ R), map (ring_hom.id R) p = p := eval₂_eta

theorem map_map [comm_semiring S₂]
  (g : S₁ →+* S₂)
  (p : mv_polynomial σ R) :
  map g (map f p) = map (g.comp f) p :=
(eval₂_comp_left (map g) (C.comp f) X p).trans $
begin
  congr,
  { ext1 a, simp only [map_C, comp_app, ring_hom.coe_comp], },
  { ext1 n, simp only [map_X, comp_app], }
end

theorem eval₂_eq_eval_map (g : σ → S₁) (p : mv_polynomial σ R) :
  p.eval₂ f g = eval g (map f p) :=
begin
  unfold map eval, simp only [coe_eval₂_hom],
  have h := eval₂_comp_left (eval₂_hom _ g),
  dsimp at h,
  rw h,
  congr,
  { ext1 a, simp only [coe_eval₂_hom, ring_hom.id_apply, comp_app, eval₂_C, ring_hom.coe_comp], },
  { ext1 n, simp only [comp_app, eval₂_X], },
end

lemma eval₂_comp_right {S₂} [comm_semiring S₂]
  (k : S₁ →+* S₂) (f : R →+* S₁) (g : σ → S₁)
  (p) : k (eval₂ f g p) = eval₂ k (k ∘ g) (map f p) :=
begin
  apply mv_polynomial.induction_on p,
  { intro r, rw [eval₂_C, map_C, eval₂_C] },
  { intros p q hp hq, rw [eval₂_add, k.map_add, (map f).map_add, eval₂_add, hp, hq] },
  { intros p s hp,
    rw [eval₂_mul, k.map_mul, (map f).map_mul, eval₂_mul, map_X, hp, eval₂_X, eval₂_X] }
end

lemma map_eval₂ (f : R →+* S₁) (g : S₂ → mv_polynomial S₃ R) (p : mv_polynomial S₂ R) :
  map f (eval₂ C g p) = eval₂ C (map f ∘ g) (map f p) :=
begin
  apply mv_polynomial.induction_on p,
  { intro r, rw [eval₂_C, map_C, map_C, eval₂_C] },
  { intros p q hp hq, rw [eval₂_add, (map f).map_add, hp, hq, (map f).map_add, eval₂_add] },
  { intros p s hp,
    rw [eval₂_mul, (map f).map_mul, hp, (map f).map_mul, map_X, eval₂_mul, eval₂_X, eval₂_X] }
end

lemma coeff_map (p : mv_polynomial σ R) : ∀ (m : σ →₀ ℕ), coeff m (map f p) = f (coeff m p) :=
begin
  apply mv_polynomial.induction_on p; clear p,
  { intros r m, rw [map_C], simp only [coeff_C], split_ifs, {refl}, rw f.map_zero },
  { intros p q hp hq m, simp only [hp, hq, (map f).map_add, coeff_add], rw f.map_add },
  { intros p i hp m, simp only [hp, (map f).map_mul, map_X],
    simp only [hp, mem_support_iff, coeff_mul_X'],
    split_ifs, {refl},
    rw is_semiring_hom.map_zero f }
end

lemma map_injective (hf : function.injective f) :
  function.injective (map f : mv_polynomial σ R → mv_polynomial σ S₁) :=
begin
  intros p q h,
  simp only [ext_iff, coeff_map] at h ⊢,
  intro m,
  exact hf (h m),
end

@[simp] lemma eval_map (f : R →+* S₁) (g : σ → S₁) (p : mv_polynomial σ R) :
  eval g (map f p) = eval₂ f g p :=
by { apply mv_polynomial.induction_on p; { simp { contextual := tt } } }

@[simp] lemma eval₂_map [comm_semiring S₂] (f : R →+* S₁) (g : σ → S₂) (φ : S₁ →+* S₂)
  (p : mv_polynomial σ R) :
  eval₂ φ g (map f p) = eval₂ (φ.comp f) g p :=
by { rw [← eval_map, ← eval_map, map_map], }

@[simp] lemma eval₂_hom_map_hom [comm_semiring S₂] (f : R →+* S₁) (g : σ → S₂) (φ : S₁ →+* S₂)
  (p : mv_polynomial σ R) :
  eval₂_hom φ g (map f p) = eval₂_hom (φ.comp f) g p :=
eval₂_map f g φ p

@[simp] lemma constant_coeff_map (f : R →+* S₁) (φ : mv_polynomial σ R) :
  constant_coeff (mv_polynomial.map f φ) = f (constant_coeff φ) :=
coeff_map f φ 0

lemma constant_coeff_comp_map (f : R →+* S₁) :
  (constant_coeff : mv_polynomial σ S₁ →+* S₁).comp (mv_polynomial.map f) = f.comp constant_coeff :=
by { ext; simp }

lemma support_map_subset (p : mv_polynomial σ R) : (map f p).support ⊆ p.support :=
begin
  intro x,
  simp only [mem_support_iff],
  contrapose!,
  change p.coeff x = 0 → (map f p).coeff x = 0,
  rw coeff_map,
  intro hx,
  rw hx,
  exact ring_hom.map_zero f
end

lemma support_map_of_injective (p : mv_polynomial σ R) {f : R →+* S₁} (hf : injective f) :
  (map f p).support = p.support :=
begin
  apply finset.subset.antisymm,
  { exact mv_polynomial.support_map_subset _ _ },
  intros x hx,
  rw mem_support_iff,
  contrapose! hx,
  simp only [not_not, mem_support_iff],
  change (map f p).coeff x = 0 at hx,
  rw [coeff_map, ← f.map_zero] at hx,
  exact hf hx
end

lemma C_dvd_iff_map_hom_eq_zero
  (q : R →+* S₁) (r : R) (hr : ∀ r' : R, q r' = 0 ↔ r ∣ r')
  (φ : mv_polynomial σ R) :
  C r ∣ φ ↔ map q φ = 0 :=
begin
  rw [C_dvd_iff_dvd_coeff, mv_polynomial.ext_iff],
  simp only [coeff_map, ring_hom.coe_of, coeff_zero, hr],
end

lemma map_map_range_eq_iff (f : R →+* S₁) (g : S₁ → R) (hg : g 0 = 0) (φ : mv_polynomial σ S₁) :
  map f (finsupp.map_range g hg φ) = φ ↔ ∀ d, f (g (coeff d φ)) = coeff d φ :=
begin
  rw mv_polynomial.ext_iff,
  apply forall_congr, intro m,
  rw [coeff_map],
  apply eq_iff_eq_cancel_right.mpr,
  refl
end

end map


section aeval

/-! ### The algebra of multivariate polynomials -/

variables (f : σ → S₁)
variables [algebra R S₁] [comm_semiring S₂]

/-- A map `σ → S₁` where `S₁` is an algebra over `R` generates an `R`-algebra homomorphism
from multivariate polynomials over `σ` to `S₁`. -/
def aeval : mv_polynomial σ R →ₐ[R] S₁ :=
{ commutes' := λ r, eval₂_C _ _ _
  .. eval₂_hom (algebra_map R S₁) f }

theorem aeval_def (p : mv_polynomial σ R) : aeval f p = eval₂ (algebra_map R S₁) f p := rfl

lemma aeval_eq_eval₂_hom (p : mv_polynomial σ R) :
  aeval f p = eval₂_hom (algebra_map R S₁) f p := rfl

@[simp] lemma aeval_X (s : σ) : aeval f (X s : mv_polynomial _ R) = f s := eval₂_X _ _ _

@[simp] lemma aeval_C (r : R) : aeval f (C r) = algebra_map R S₁ r := eval₂_C _ _ _

theorem aeval_unique (φ : mv_polynomial σ R →ₐ[R] S₁) :
  φ = aeval (φ ∘ X) :=
by { ext i, simp }

lemma comp_aeval {B : Type*} [comm_semiring B] [algebra R B]
  (φ : S₁ →ₐ[R] B) :
  φ.comp (aeval f) = aeval (λ i, φ (f i)) :=
by { ext i, simp }

@[simp] lemma map_aeval {B : Type*} [comm_semiring B]
  (g : σ → S₁) (φ : S₁ →+* B) (p : mv_polynomial σ R) :
  φ (aeval g p) = (eval₂_hom (φ.comp (algebra_map R S₁)) (λ i, φ (g i)) p) :=
by { rw ← comp_eval₂_hom, refl }

@[simp] lemma eval₂_hom_zero (f : R →+* S₂) (p : mv_polynomial σ R) :
  eval₂_hom f (0 : σ → S₂) p = f (constant_coeff p) :=
begin
  suffices : eval₂_hom f (0 : σ → S₂) = f.comp constant_coeff,
    from ring_hom.congr_fun this p,
  ext; simp
end

@[simp] lemma eval₂_hom_zero' (f : R →+* S₂) (p : mv_polynomial σ R) :
  eval₂_hom f (λ _, 0 : σ → S₂) p = f (constant_coeff p) :=
eval₂_hom_zero f p

@[simp] lemma aeval_zero (p : mv_polynomial σ R) :
  aeval (0 : σ → S₁) p = algebra_map _ _ (constant_coeff p) :=
eval₂_hom_zero (algebra_map R S₁) p

@[simp] lemma aeval_zero' (p : mv_polynomial σ R) :
  aeval (λ _, 0 : σ → S₁) p = algebra_map _ _ (constant_coeff p) :=
aeval_zero p

lemma aeval_monomial (g : σ → S₁) (d : σ →₀ ℕ) (r : R) :
  aeval g (monomial d r) = algebra_map _ _ r * d.prod (λ i k, g i ^ k) :=
eval₂_hom_monomial _ _ _ _

lemma eval₂_hom_eq_zero (f : R →+* S₂) (g : σ → S₂) (φ : mv_polynomial σ R)
  (h : ∀ d, φ.coeff d ≠ 0 → ∃ i ∈ d.support, g i = 0) :
  eval₂_hom f g φ = 0 :=
begin
  rw [φ.as_sum, ring_hom.map_sum, finset.sum_eq_zero],
  intros d hd,
  obtain ⟨i, hi, hgi⟩ : ∃ i ∈ d.support, g i = 0 := h d (finsupp.mem_support_iff.mp hd),
  rw [eval₂_hom_monomial, finsupp.prod, finset.prod_eq_zero hi, mul_zero],
  rw [hgi, zero_pow],
  rwa [pos_iff_ne_zero, ← finsupp.mem_support_iff]
end

lemma aeval_eq_zero [algebra R S₂] (f : σ → S₂) (φ : mv_polynomial σ R)
  (h : ∀ d, φ.coeff d ≠ 0 → ∃ i ∈ d.support, f i = 0) :
  aeval f φ = 0 :=
eval₂_hom_eq_zero _ _ _ h

end aeval

end comm_semiring

end mv_polynomial
