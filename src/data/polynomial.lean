/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker, Yury Kudryashov
-/
import data.monoid_algebra
import algebra.gcd_domain
import ring_theory.euclidean_domain
import ring_theory.multiplicity
import tactic.ring_exp
import deprecated.field

/-!
# Theory of univariate polynomials

Polynomials are represented as `add_monoid_algebra R ℕ`, where `R` is a commutative semiring.
-/

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

universes u v w x y z
variables {R : Type u} {S : Type v} {T : Type w} {A : Type x} {B : Type y} {ι : Type z}

/-- `polynomial R` is the type of univariate polynomials over `R`.

Polynomials should be seen as (semi-)rings with the additional constructor `X`.
The embedding from `R` is called `C`. -/
def polynomial (R : Type*) [comm_semiring R] := add_monoid_algebra R ℕ

open finsupp finset add_monoid_algebra

namespace polynomial

variables [comm_semiring R] {a b : R} {m n : ℕ} {p q r : polynomial R}

instance : inhabited (polynomial R) := finsupp.inhabited
instance : comm_semiring (polynomial R) := add_monoid_algebra.comm_semiring
instance : algebra R (polynomial R) := add_monoid_algebra.algebra

@[simp] lemma support_zero : (0 : polynomial R).support = ∅ := rfl

/-- `monomial s a` is the monomial `a * X^s` -/
def monomial (n : ℕ) (a : R) : polynomial R := finsupp.single n a

@[simp] lemma single_eq_monomial (n : ℕ) (a : R) :
  single n a = monomial n a := rfl

lemma smul_monomial : a • monomial n b = monomial n (a * b) :=
smul_single _ _ _

lemma support_monomial_ne_zero (hb : b ≠ 0) : (monomial n b).support = {n} :=
support_single_ne_zero hb

@[simp] lemma monomial_zero : monomial n (0 : R) = 0 := finsupp.single_zero

/-- `C R a` is the constant polynomial `a`. -/
def C (R : Type u) [comm_semiring R] : R →ₐ[R] polynomial R :=
algebra.of_id R (polynomial R)

lemma C_def : C R a = monomial 0 a := rfl

/-- `C a * p = a • p`. Non-primed version says `C (a * b) = C a * C b`. -/
lemma C_mul' : C R a * p = a • p := (algebra.smul_def _ _).symm

/-- `X` is the polynomial variable (aka indeterminant). -/
def X : polynomial R := monomial 1 1

/-- coeff p n is the coefficient of X^n in p -/
def coeff (p : polynomial R) (n : ℕ) := (@coe_fn (ℕ →₀ R) _ p : ℕ → R) n

@[simp] lemma coeff_mk (s) (f) (h) : coeff (finsupp.mk s f h : polynomial R) = f := rfl

instance [has_repr R] : has_repr (polynomial R) :=
⟨λ p, if p = 0 then "0"
  else (p.support.sort (≤)).foldr
    (λ n a, a ++ (if a = "" then "" else " + ") ++
      if n = 0
        then "C (" ++ repr (coeff p n) ++ ")"
        else if n = 1
          then if (coeff p n) = 1 then "X" else "C (" ++ repr (coeff p n) ++ ") * X"
          else if (coeff p n) = 1 then "X ^ " ++ repr n
            else "C (" ++ repr (coeff p n) ++ ") * X ^ " ++ repr n) ""⟩

theorem ext_iff {p q : polynomial R} : p = q ↔ ∀ n, coeff p n = coeff q n :=
⟨λ h n, h ▸ rfl, finsupp.ext⟩

@[ext] lemma ext {p q : polynomial R} : (∀ n, coeff p n = coeff q n) → p = q :=
ext_iff.2

/-- `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`.
`degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise
`degree 0 = ⊥`. -/
def degree (p : polynomial R) : with_bot ℕ := p.support.sup coe

lemma degree_lt_wf : well_founded (λp q : polynomial R, degree p < degree q) :=
inv_image.wf degree (with_bot.well_founded_lt nat.lt_wf)

instance : has_well_founded (polynomial R) := ⟨_, degree_lt_wf⟩

/-- `nat_degree p` forces `degree p` to ℕ, by defining nat_degree 0 = 0. -/
def nat_degree (p : polynomial R) : ℕ := (degree p).get_or_else 0

lemma monomial_mul_monomial : monomial m a * monomial n b = monomial (m + n) (a * b) :=
single_mul_single

/-- `(a * X^m)^n = a^n * X^(n * m)`-/
lemma pow_monomial : (monomial m a)^n = monomial (n * m) (a ^ n) :=
by rw [monomial, monomial, single_pow, nat.smul_eq_mul]

lemma pow_X : (X^n : polynomial R) = monomial n 1 := by rw [X, pow_monomial, mul_one, one_pow]

lemma monomial_eq_C_mul_X {n} : monomial n a = C R a * X^n :=
by rw [pow_X, C_mul', smul_monomial, mul_one]

lemma sum_monomial (p : polynomial R) : p.sum monomial = p := p.sum_single

lemma sum_C_mul_X_eq (p : polynomial R) : p.sum (λn a, C R a * X^n) = p :=
calc p.sum (λn a, C R a * X^n) = p.sum monomial :
  sum_congr rfl $ assume n hn, monomial_eq_C_mul_X.symm
... = _ : sum_monomial _

@[elab_as_eliminator] protected lemma induction_on {M : polynomial R → Prop} (p : polynomial R)
  (h_C : ∀a, M (C R a))
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_monomial : ∀(n : ℕ) (a : R), M (C R a * X^n) → M (C R a * X^(n+1))) :
  M p :=
have ∀{n:ℕ} {a}, M (C R a * X^n),
begin
  assume n a,
  induction n with n ih,
  { simp only [pow_zero, mul_one, h_C] },
  { exact h_monomial _ _ ih }
end,
finsupp.induction p
  (suffices M (C R 0), by { convert this, exact single_zero.symm, },
    h_C 0)
  (assume n a p _ _ hp,
    suffices M (C R a * X^n + p), by { convert this, exact monomial_eq_C_mul_X },
    h_add _ _ this hp)

lemma add_hom_ext [add_monoid A] ⦃f g : polynomial R →+ A⦄
  (H : ∀ n a, f (monomial n a) = g (monomial n a)) : f = g :=
add_monoid_algebra.add_hom_ext H

lemma semimodule_linear_map_ext [add_comm_monoid A] [semimodule R A] ⦃f g : polynomial R →+ A⦄
  (hf : ∀ (c : R) p, f (c • p) = c • f p) (hg : ∀ (c : R) p, g (c • p) = c • g p)
  (H : ∀ n : ℕ, f (X ^ n) = g (X ^ n)) : f = g :=
add_monoid_algebra.semimodule_linear_map_ext hf hg $ by simpa only [pow_X] using H

lemma ring_hom_ext [semiring S] ⦃f g : polynomial R →+* S⦄ (HC : ∀ a, f (C R a) = g (C R a))
  (HX : f X = g X) : f = g :=
ring_hom.coe_add_monoid_hom_inj $ add_hom_ext $ λ n a, by simp [*, monomial_eq_C_mul_X]

lemma C_0 : C R 0 = 0 := single_zero

lemma C_1 : C R 1 = 1 := rfl

lemma C_mul : C R (a * b) = C R a * C R b :=
(C R).map_mul a b

lemma C_add : C R (a + b) = C R a + C R b := (C R).map_add a b

lemma C_pow : C R (a ^ n) = C R a ^ n := (C R).map_pow a n

lemma nat_cast_eq_C (n : ℕ) : (n : polynomial R) = C R n :=
((C R).to_ring_hom.map_nat_cast n).symm

section coeff

@[simp] lemma coeff_zero (n : ℕ) : coeff (0 : polynomial R) n = 0 := rfl

lemma coeff_monomial {n : ℕ} :
  coeff (monomial n a) m = if m = n then a else 0 :=
by { convert finsupp.single_apply using 2, exact propext eq_comm }

@[simp] lemma coeff_one_zero : coeff (1 : polynomial R) 0 = 1 :=
coeff_monomial

@[simp]
lemma coeff_add (p q : polynomial R) (n : ℕ) : coeff (p + q) n = coeff p n + coeff q n := rfl

variable (R)

/-- `coeff` as an `add_monoid_hom`. Actually it is a linear map but we have no `linear_map`s on
`semimodule`s. -/
def coeff_add_hom (n : ℕ) : polynomial R →+ R := ⟨λ p, p.coeff n, coeff_zero n, λ p q, coeff_add p q n⟩

variable {R}

@[simp] lemma coeff_add_hom_apply (n : ℕ)  : coeff_add_hom R n p = p.coeff n := rfl

lemma coeff_C : coeff (C R a) n = ite (n = 0) a 0 :=
by { rw [C_def], exact coeff_monomial }

@[simp] lemma coeff_C_zero : coeff (C R a) 0 = a := coeff_monomial

@[simp] lemma coeff_X_one : coeff (X : polynomial R) 1 = 1 := coeff_monomial

@[simp] lemma coeff_X_zero : coeff (X : polynomial R) 0 = 0 := coeff_monomial

lemma coeff_X : coeff (X : polynomial R) n = if n = 1 then 1 else 0 := coeff_monomial

lemma coeff_sum [comm_semiring S] (n : ℕ) (f : ℕ → R → polynomial S) :
  coeff (p.sum f) n = p.sum (λ a b, coeff (f a b) n) := finsupp.sum_apply

@[simp] lemma coeff_smul (p : polynomial R) (r : R) (n : ℕ) :
  coeff (r • p) n = r * coeff p n :=
finsupp.smul_apply

@[simp] lemma coeff_C_mul (p : polynomial R) :
  coeff (C R a * p) n = a * coeff p n :=
by rw [C_mul', coeff_smul]

@[simp] lemma coeff_X_pow (k n : ℕ) :
  coeff (X^k : polynomial R) n = if n = k then 1 else 0 :=
by rw [pow_X, coeff_monomial]

lemma coeff_C_mul_X (x : R) (k n : ℕ) :
  coeff (C R x * X^k) n = if n = k then x else 0 :=
by rw [← monomial_eq_C_mul_X, coeff_monomial]

@[simp, priority 990]
lemma coeff_one (n : ℕ) :
  coeff (1 : polynomial R) n = if n = 0 then 1 else 0 :=
coeff_C

lemma coeff_mul (p q : polynomial R) (n : ℕ) :
  coeff (p * q) n = (nat.antidiagonal n).sum (λ x, coeff p x.1 * coeff q x.2) :=
mul_apply_antidiagonal _ _ _ _ (λ _, nat.mem_antidiagonal)

theorem coeff_mul_X_pow (p : polynomial R) (n d : ℕ) :
  coeff (p * polynomial.X ^ n) (d + n) = coeff p d :=
begin
  rw [pow_X, coeff, monomial, ← mul_one (coeff p d)],
  exact p.mul_single_apply_aux (λ a, add_right_cancel_iff)
end

theorem coeff_mul_X (p : polynomial R) (n : ℕ) :
  coeff (p * X) (n + 1) = coeff p n :=
pow_one (X : polynomial R) ▸ coeff_mul_X_pow p 1 n

theorem mul_X_pow_eq_zero {p : polynomial R} {n : ℕ}
  (H : p * X ^ n = 0) : p = 0 :=
ext $ λ k, (coeff_mul_X_pow p n k).symm.trans $ ext_iff.1 H (k+n)

end coeff

lemma C_inj : C R a = C R b ↔ a = b := (finsupp.injective_single _).eq_iff

section aeval

variables (R) (A) [semiring A] [algebra R A] [semiring B] [algebra R B] {x : A}

/-- Given a valuation `x` of the variable in an `R`-algebra `A`, `aeval R A x` is
the unique `R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`. -/
def aeval : A ≃ (polynomial R →ₐ[R] A) := (powers_hom A).trans (add_monoid_algebra.lift R ℕ A)

variables {R A}

theorem aeval_def' : aeval R A x p = add_monoid_algebra.lift R ℕ A (powers_hom A x) p := rfl

theorem aeval_def : aeval R A x p = p.sum (λ n a, a • x^n) := rfl

-- Not `rfl` because of `to_add`/`of_add`
@[simp] theorem aeval_symm_apply (φ : polynomial R →ₐ[R] A) : (aeval R A).symm φ = φ X :=
by rw [aeval]; simp [X]

@[simp] lemma aeval_monomial :
  aeval R A x (monomial n a) = a • x ^ n :=
lift_single _ _ _

@[simp] lemma aeval_X : aeval R A x X = x :=
by rw [← aeval_symm_apply, equiv.symm_apply_apply]

@[simp] lemma aeval_C : aeval R A x (C R a) = algebra_map R A a :=
(aeval R A x).commutes a

lemma aeval_add : aeval R A x (p + q) = aeval R A x p + aeval R A x q :=
(aeval R A x).map_add p q

lemma aeval_smul : aeval R A x (a • p) = a • aeval R A x p :=
(aeval R A x).map_smul a p

lemma aeval_mul : aeval R A x (p * q) = aeval R A x p * aeval R A x q :=
(aeval R A x).map_mul p q

lemma aeval_sum (f : ℕ → R → polynomial R) :
  aeval R A x (p.sum f) = p.sum (λ n a, aeval R A x (f n a)) :=
(aeval R A x).map_sum _ _

theorem alg_hom_ext ⦃φ φ' : polynomial R →ₐ[R] A⦄ (h : φ X = φ' X) :
  φ = φ' :=
(aeval R A).symm.injective $ by simpa only [aeval_symm_apply]

theorem aeval_unique' (φ : polynomial R →ₐ[R] A) : φ = aeval R A (φ X) :=
alg_hom_ext $ aeval_X.symm

theorem aeval_unique (φ : polynomial R →ₐ[R] A) : φ p = aeval R A (φ X) p :=
congr_fun (congr_arg _ $ aeval_unique' φ) p

theorem aeval_zero_eq_coeff_zero' : aeval R A 0 p = (coeff p 0) • 1 :=
lift_zero (λ n hn, zero_pow $ bot_lt_iff_ne_bot.2 hn) _

theorem aeval_zero_eq_coeff_zero : aeval R A 0 p = algebra_map R A (coeff p 0) :=
by rw [aeval_zero_eq_coeff_zero', algebra.smul_def, mul_one]

theorem aeval_hom' (φ : A →ₐ[R] B) : aeval R B (φ x) = φ.comp (aeval R A x) :=
alg_hom_ext $ by simp only [aeval_X, alg_hom.comp_apply]

theorem aeval_hom (φ : A →ₐ[R] B) : aeval R B (φ x) p = φ (aeval R A x p) :=
by rw [aeval_hom', alg_hom.comp_apply]

/-- `is_root p x` implies `x` is a root of `p`. The evaluation of `p` at `x` is zero -/
def is_root (p : polynomial R) (x : A) : Prop := aeval R A x p = 0

instance [decidable_eq A] : decidable (is_root p a) := by unfold is_root; apply_instance

lemma is_root.eq (h : is_root p x) : aeval R A x p = 0 := h

lemma is_root_def : is_root p x ↔ aeval R A x p = 0 := iff.rfl

lemma is_root.mul_left (p : polynomial R) (h : is_root q x) :
  is_root (p * q) x :=
by simp [is_root, h.eq]

lemma is_root.mul_right (h : is_root p x) (q : polynomial R) :
  is_root (p * q) x :=
by simp [is_root, h.eq]

lemma is_root_zero' : is_root p (0:A) ↔ algebra_map R A (coeff p 0) = 0 :=
eq_iff_eq_cancel_right.2 aeval_zero_eq_coeff_zero

end aeval

section eval₂
variables [comm_semiring S]
variables (f : R →+* S) (x : S)

/-- Evaluate a polynomial `p` given a ring hom `f` from the scalar ring
  to the target and a value `x` for the variable in the target -/
def eval₂ : polynomial R →+* S := @aeval R S _ _ f.to_algebra x

lemma eval₂_def : eval₂ f x p = p.sum (λ n a, f a * x ^ n) := rfl

@[simp] lemma eval₂_C : eval₂ f x (C R a) = f a :=
@aeval_C _ _ _ _ _ f.to_algebra _

@[simp] lemma eval₂_X : eval₂ f x X = x :=
@aeval_X _ _ _ _ f.to_algebra _

@[simp] lemma eval₂_monomial : eval₂ f x (monomial n a) = f a * x ^ n :=
@aeval_monomial _ _ _ _ _ _ f.to_algebra _

lemma eval₂_zero : eval₂ f x 0 = 0 := ring_hom.map_zero _

lemma eval₂_add : eval₂ f x (p + q) = eval₂ f x p + eval₂ f x q :=
ring_hom.map_add _ _ _

lemma eval₂_one : eval₂ f x 1 = 1 := ring_hom.map_one _

lemma eval₂_mul : eval₂ f x (p * q) = eval₂ f x p * eval₂ f x q :=
ring_hom.map_mul _ _ _

lemma eval₂_pow (n : ℕ) : eval₂ f x (p ^ n) = eval₂ f x p ^ n :=
ring_hom.map_pow _ _ _

lemma eval₂_sum (p : polynomial R) (g : ℕ → R → polynomial R) (x : S) :
  eval₂ f x (p.sum g) = p.sum (λ n a, eval₂ f x (g n a)) :=
@aeval_sum _ _ _ _ _ f.to_algebra _ _

end eval₂

section eval
variables (R) {x : R}

/-- `eval x p` is the evaluation of the polynomial `p` at `x` -/
def eval : R ≃ (polynomial R →ₐ[R] R) := aeval R R

variable {R}

@[simp] lemma eval_C : eval R x (C R a) = a := aeval_C

@[simp] lemma eval_X : eval R x X = x := aeval_X

lemma eval_sum (p : polynomial R) (f : ℕ → R → polynomial R) (x : R) :
  eval R x (p.sum f) = p.sum (λ n a, eval R x (f n a)) :=
(eval R x).map_sum _ _

lemma coeff_zero_eq_eval_zero : coeff p 0 = eval R 0 p :=
(@aeval_zero_eq_coeff_zero R R _ p _ _).symm

lemma is_root_zero : is_root p (0:R) ↔ coeff p 0 = 0 := is_root_zero'

end eval

section comp

/-- Composition of polynomials. -/
def comp (p q : polynomial R) : polynomial R :=
(aeval R (polynomial R) : polynomial R → polynomial R →ₐ[R] polynomial R) q p

lemma aeval_comp [semiring A] [algebra R A] (x : A) :
  aeval R A x (p.comp q) = aeval R A (aeval R A x q) p :=
by rw [comp, aeval_hom]

lemma eval_comp : eval R a (p.comp q) = eval R (eval R a q) p :=
aeval_comp _

@[simp] lemma comp_X : p.comp X = p := (aeval_unique (alg_hom.id _ _)).symm

@[simp] lemma X_comp : X.comp p = p := aeval_X

@[simp] lemma comp_C : p.comp (C R a) = C R (eval R a p) := aeval_hom (C R)

@[simp] lemma C_comp : (C R a).comp p = C R a := aeval_C

@[simp] lemma comp_zero : p.comp (0 : polynomial R) = C R (eval R 0 p) :=
by rw [← C_0, comp_C]

@[simp] lemma zero_comp : comp (0 : polynomial R) p = 0 :=
by rw [← C_0, C_comp]

@[simp] lemma comp_one : p.comp 1 = C R (eval R 1 p) :=
by rw [← C_1, comp_C]

@[simp] lemma one_comp : comp (1 : polynomial R) p = 1 :=
by rw [← C_1, C_comp]

@[simp] lemma add_comp : (p + q).comp r = p.comp r + q.comp r := aeval_add
@[simp] lemma mul_comp : (p * q).comp r = p.comp r * q.comp r := aeval_mul
@[simp] lemma smul_comp : (a • p).comp r = a • (p.comp r) := aeval_smul
@[simp] lemma sum_comp (f : ℕ → R → polynomial R) :
  (p.sum f).comp r = p.sum (λ n a, (f n a).comp r) :=
aeval_sum _

end comp

/-- `leading_coeff p` gives the coefficient of the highest power of `X` in `p`-/
def leading_coeff (p : polynomial R) : R := coeff p (nat_degree p)

/-- a polynomial is `monic` if its leading coefficient is 1 -/
def monic (p : polynomial R) := leading_coeff p = 1

lemma monic.def : monic p ↔ leading_coeff p = 1 := iff.rfl

instance monic.decidable [decidable_eq R] : decidable (monic p) :=
by unfold monic; apply_instance

@[simp] lemma monic.leading_coeff {p : polynomial R} (hp : p.monic) :
  leading_coeff p = 1 := hp

@[simp] lemma degree_zero : degree (0 : polynomial R) = ⊥ := rfl

@[simp] lemma nat_degree_zero : nat_degree (0 : polynomial R) = 0 := rfl

@[simp] lemma degree_monomial (ha : a ≠ 0) : degree (monomial n a) = n :=
by rw [degree, support_monomial_ne_zero ha, finset.sup_singleton]

@[simp] lemma degree_C (ha : a ≠ 0) : degree (C R a) = (0 : with_bot ℕ) :=
degree_monomial ha

@[simp] lemma degree_le_nat_degree : degree p ≤ nat_degree p :=
with_bot.le_coe_get_or_else _ _

lemma degree_monomial_le : degree (monomial n a) ≤ n :=
if h : a = 0 then by { rw [h, monomial_zero, degree_zero], exact bot_le }
else le_of_eq (degree_monomial h)

@[simp] lemma nat_degree_C (a : R) : nat_degree (C R a) = 0 :=
if ha : a = 0 then (by simp [ha]) else (by rw [nat_degree, degree_C ha]; refl)

lemma degree_C_le : degree (C R a) ≤ (0 : with_bot ℕ) :=
degree_monomial_le

lemma degree_one_le : degree (1 : polynomial R) ≤ (0 : with_bot ℕ) := degree_C_le

lemma degree_eq_bot : degree p = ⊥ ↔ p = 0 :=
max_eq_none.trans support_eq_empty

lemma degree_eq_nat_degree (hp : p ≠ 0) : degree p = (nat_degree p : with_bot ℕ) :=
(option.get_or_else_of_ne_none (mt degree_eq_bot.1 hp) 0).symm

lemma degree_eq_iff_nat_degree_eq {p : polynomial R} {n : ℕ} (hp : p ≠ 0) :
  p.degree = n ↔ p.nat_degree = n :=
by rw [degree_eq_nat_degree hp, with_bot.coe_eq_coe]

lemma degree_eq_iff_nat_degree_eq_of_pos {p : polynomial R} {n : ℕ} (hn : n > 0) :
  p.degree = n ↔ p.nat_degree = n :=
begin
  split,
  { intro H, rwa ← degree_eq_iff_nat_degree_eq, rintro rfl,
    rw degree_zero at H, exact option.no_confusion H },
  { intro H, rwa degree_eq_iff_nat_degree_eq, rintro rfl,
    rw nat_degree_zero at H, rw H at hn, exact lt_irrefl _ hn }
end

lemma nat_degree_eq_of_degree_eq_some {p : polynomial R} {n : ℕ}
  (h : degree p = n) : nat_degree p = n :=
by { rw [nat_degree, h], refl }

lemma nat_degree_eq_of_degree_eq [comm_semiring S] {q : polynomial S}
  (h : degree p = degree q) : nat_degree p = nat_degree q :=
by { unfold nat_degree, rw h }

lemma le_degree_of_ne_zero (h : coeff p n ≠ 0) : (n : with_bot ℕ) ≤ degree p :=
show @has_le.le (with_bot ℕ) _ (some n : with_bot ℕ) (p.support.sup some : with_bot ℕ),
from finset.le_sup (finsupp.mem_support_iff.2 h)

lemma le_nat_degree_of_ne_zero (h : coeff p n ≠ 0) : n ≤ nat_degree p :=
begin
  rw [← with_bot.coe_le_coe, ← degree_eq_nat_degree],
  exact le_degree_of_ne_zero h,
  { assume h, subst h, exact h rfl }
end

lemma degree_le_degree (h : coeff q (nat_degree p) ≠ 0) : degree p ≤ degree q :=
begin
  by_cases hp : p = 0,
  { rw hp, exact bot_le },
  { rw degree_eq_nat_degree hp, exact le_degree_of_ne_zero h }
end

@[simp] lemma nat_degree_one : nat_degree (1 : polynomial R) = 0 := nat_degree_C 1

@[simp] lemma nat_degree_nat_cast (n : ℕ) : nat_degree (n : polynomial R) = 0 :=
by simp [nat_cast_eq_C]

lemma coeff_eq_zero_of_degree_lt (h : degree p < n) : coeff p n = 0 :=
not_not.1 (mt le_degree_of_ne_zero (not_le_of_gt h))

lemma coeff_eq_zero_of_nat_degree_lt {p : polynomial R} {n : ℕ} (h : p.nat_degree < n) :
  p.coeff n = 0 :=
begin
  refine coeff_eq_zero_of_degree_lt (lt_of_le_of_lt degree_le_nat_degree _),
  rwa with_bot.coe_lt_coe,
end

-- TODO find a home (this file)
@[simp] lemma finset_sum_coeff (s : finset ι) (f : ι → polynomial R) (n : ℕ) :
  coeff (s.sum f) n = s.sum (λ b, coeff (f b) n) :=
(s.sum_hom (λ q : polynomial R, q.coeff n)).symm

-- We need the explicit `decidable` argument here because an exotic one shows up in a moment!
lemma ite_le_nat_degree_coeff (p : polynomial R) (n : ℕ) [decidable (n < 1 + nat_degree p)] :
  (if n < 1 + nat_degree p then coeff p n else 0) = coeff p n :=
begin
  split_ifs,
  { refl },
  { exact (coeff_eq_zero_of_nat_degree_lt (not_le.1 (λ w, h (nat.lt_one_add_iff.2 w)))).symm, }
end

lemma as_sum (p : polynomial R) :
  p = (range (p.nat_degree + 1)).sum (λ i, C R (p.coeff i) * X^i) :=
begin
  ext n,
  simp only [add_comm, coeff_X_pow, coeff_C_mul, finset.mem_range,
    finset.sum_mul_boole, finset_sum_coeff, ite_le_nat_degree_coeff]
end

lemma monic.as_sum {p : polynomial R} (hp : p.monic) :
  p = X^(p.nat_degree) + ((finset.range p.nat_degree).sum $ λ i, C R (p.coeff i) * X^i) :=
begin
  conv_lhs { rw [p.as_sum, finset.sum_range_succ] },
  suffices : C R (p.coeff p.nat_degree) = 1,
  { rw [this, one_mul] },
  exact congr_arg (C R) hp
end

section map
variables [comm_semiring S]
variables (f : R →+* S)

/-- `map f p` maps a polynomial `p` across a ring hom `f` -/
def map : polynomial R →+* polynomial S := eval₂ ((C S : S →+* polynomial S).comp f) X

lemma map_def : map f p = eval₂ ((C S : S →+* polynomial S).comp f) X p := rfl

@[simp] lemma map_C : map f (C R a) = C S (f a) := eval₂_C _ _

@[simp] lemma map_X : map f X = X := eval₂_X _ _

lemma map_zero : map f 0 = 0 :=  eval₂_zero _ _

lemma map_add : map f (p + q) = map f p + map f q := eval₂_add _ _

lemma map_one : map f 1 = 1 := eval₂_one _ _

lemma map_mul : map f (p * q) = map f p * map f q := eval₂_mul _ _

lemma map_pow (n : ℕ) : map f (p ^ n) = map f p ^ n := eval₂_pow _ _ _

@[simp] lemma map_monomial : map f (monomial n a) = monomial n (f a) :=
by simp [map_def, eval₂_monomial, ← monomial_eq_C_mul_X]

lemma map_sum [comm_semiring T] (p : polynomial T) (g : ℕ → T → polynomial R) :
  map f (p.sum g) = p.sum (λ n a, map f (g n a)) :=
(map f).map_sum _ _

lemma coeff_map (n : ℕ) : coeff (map f p) n = f (coeff p n) :=
finsupp.induction p (by simp) $ λ k a f hk ha hf,
by by_cases hnk : n = k; simp [coeff_monomial, hf]; simp [hnk]

lemma map_comp [comm_semiring T] (g : S →+* T) :
  map (g.comp f) = (map g).comp (map f) :=
ring_hom_ext (λ a, by simp only [map_C, ring_hom.comp_apply])
  (by simp only [map_X, ring_hom.comp_apply])

lemma map_map [comm_semiring T] (g : S →+* T) :
  map g (map f p) = map (g.comp f) p :=
by rw [map_comp, ring_hom.comp_apply]

lemma eval₂_comp [comm_semiring T] (g : S →+* T) (x : T) :
  eval₂ (g.comp f) x = (eval₂ g x).comp (map f) :=
ring_hom_ext (λ a, by simp only [eval₂_C, map_C, ring_hom.comp_apply]) $
  by simp only [map_X, eval₂_X, ring_hom.comp_apply]

lemma eval₂_map [comm_semiring T] (g : S →+* T) (x : T) :
  eval₂ g x (map f p) = eval₂ (g.comp f) x p :=
by rw [eval₂_comp, ring_hom.comp_apply]

lemma eval_map (x : S) : eval S x (map f p) = eval₂ f x p := eval₂_map _ _ _

@[simp] lemma map_id : p.map (ring_hom.id _) = p := by simp [polynomial.ext_iff, coeff_map]

lemma mem_map_range {p : polynomial S} :
  p ∈ set.range (map f) ↔ ∀ n, p.coeff n ∈ (set.range f) :=
begin
  split,
  { rintro ⟨p, rfl⟩ n, rw coeff_map, exact set.mem_range_self _ },
  { intro h, rw p.as_sum,
    apply is_add_submonoid.finset_sum_mem,
    intros i hi,
    rcases h i with ⟨c, hc⟩,
    use [C c * X^i],
    rw [map_mul, map_C, hc, map_pow, map_X] }
end

end map

section
variables [comm_semiring S] [comm_semiring T]
variables (f : R →+* S) (g : S →+* T) (p)

lemma hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g ∘ f) (g x) :=
begin
  apply polynomial.induction_on p; clear p,
  { intros a, rw [eval₂_C, eval₂_C] },
  { intros p q hp hq, simp only [hp, hq, eval₂_add, is_semiring_hom.map_add g] },
  { intros n a ih,
    replace ih := congr_arg (λ y, y * g x) ih,
    simpa [pow_succ', is_semiring_hom.map_mul g, (mul_assoc _ _ _).symm,
      eval₂_C, eval₂_mul, eval₂_X] using ih }
end

end

lemma coeff_nat_degree_eq_zero_of_degree_lt (h : degree p < degree q) :
  coeff p (nat_degree q) = 0 :=
coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h degree_le_nat_degree)

lemma ne_zero_of_degree_gt {n : with_bot ℕ} (h : n < degree p) : p ≠ 0 :=
mt degree_eq_bot.2 (ne.symm (ne_of_lt (lt_of_le_of_lt bot_le h)))

lemma eq_C_of_degree_le_zero (h : degree p ≤ 0) : p = C (coeff p 0) :=
begin
  refine ext (λ n, _),
  cases n,
  { simp },
  { have : degree p < ↑(nat.succ n) := lt_of_le_of_lt h (with_bot.some_lt_some.2 (nat.succ_pos _)),
    rw [coeff_C, if_neg (nat.succ_ne_zero _), coeff_eq_zero_of_degree_lt this] }
end

lemma eq_C_of_degree_eq_zero (h : degree p = 0) : p = C (coeff p 0) :=
eq_C_of_degree_le_zero (h ▸ le_refl _)

lemma degree_le_zero_iff : degree p ≤ 0 ↔ p = C (coeff p 0) :=
⟨eq_C_of_degree_le_zero, λ h, h.symm ▸ degree_C_le⟩

lemma degree_add_le (p q : polynomial R) : degree (p + q) ≤ max (degree p) (degree q) :=
calc degree (p + q) = ((p + q).support).sup some : rfl
  ... ≤ (p.support ∪ q.support).sup some : by convert sup_mono support_add
  ... = p.support.sup some ⊔ q.support.sup some : by convert sup_union
  ... = _ : with_bot.sup_eq_max _ _

@[simp] lemma leading_coeff_zero : leading_coeff (0 : polynomial R) = 0 := rfl

@[simp] lemma leading_coeff_eq_zero : leading_coeff p = 0 ↔ p = 0 :=
⟨λ h, by_contradiction $ λ hp, mt mem_support_iff.1
  (not_not.2 h) (mem_of_max (degree_eq_nat_degree hp)),
λ h, h.symm ▸ leading_coeff_zero⟩

lemma leading_coeff_eq_zero_iff_deg_eq_bot : leading_coeff p = 0 ↔ degree p = ⊥ :=
by rw [leading_coeff_eq_zero, degree_eq_bot]

lemma degree_add_eq_of_degree_lt (h : degree p < degree q) : degree (p + q) = degree q :=
le_antisymm (max_eq_right_of_lt h ▸ degree_add_le _ _) $ degree_le_degree $
  begin
    rw [coeff_add, coeff_nat_degree_eq_zero_of_degree_lt h, zero_add],
    exact mt leading_coeff_eq_zero.1 (ne_zero_of_degree_gt h)
  end

lemma degree_add_C (hp : 0 < degree p) : degree (p + C a) = degree p :=
add_comm (C a) p ▸ degree_add_eq_of_degree_lt $ lt_of_le_of_lt degree_C_le hp

lemma degree_add_eq_of_leading_coeff_add_ne_zero (h : leading_coeff p + leading_coeff q ≠ 0) :
  degree (p + q) = max p.degree q.degree :=
le_antisymm (degree_add_le _ _) $
  match lt_trichotomy (degree p) (degree q) with
  | or.inl hlt :=
    by rw [degree_add_eq_of_degree_lt hlt, max_eq_right_of_lt hlt]; exact le_refl _
  | or.inr (or.inl heq) :=
    le_of_not_gt $
      assume hlt : max (degree p) (degree q) > degree (p + q),
      h $ show leading_coeff p + leading_coeff q = 0,
      begin
        rw [heq, max_self] at hlt,
        rw [leading_coeff, leading_coeff, nat_degree_eq_of_degree_eq heq, ← coeff_add],
        exact coeff_nat_degree_eq_zero_of_degree_lt hlt
      end
  | or.inr (or.inr hlt) :=
    by rw [add_comm, degree_add_eq_of_degree_lt hlt, max_eq_left_of_lt hlt]; exact le_refl _
  end

lemma degree_erase_le (p : polynomial R) (n : ℕ) : degree (p.erase n) ≤ degree p :=
by convert sup_mono (erase_subset _ _)

lemma degree_erase_lt (hp : p ≠ 0) : degree (p.erase (nat_degree p)) < degree p :=
lt_of_le_of_ne (degree_erase_le _ _) $
  (degree_eq_nat_degree hp).symm ▸ (by convert λ h, not_mem_erase _ _ (mem_of_max h))

lemma degree_sum_le (s : finset ι) (f : ι → polynomial R) :
  degree (s.sum f) ≤ s.sup (λ b, degree (f b)) :=
finset.induction_on s (by simp only [sum_empty, sup_empty, degree_zero, le_refl]) $
  assume a s has ih,
  calc degree ((insert a s).sum f) ≤ max (degree (f a)) (degree (s.sum f)) :
    by rw sum_insert has; exact degree_add_le _ _
  ... ≤ _ : by rw [sup_insert, with_bot.sup_eq_max]; exact max_le_max (le_refl _) ih

lemma degree_mul_le (p q : polynomial R) : degree (p * q) ≤ degree p + degree q :=
calc degree (p * q) ≤ (p.support).sup (λi, degree (sum q (λj a, C (coeff p i * a) * X ^ (i + j)))) :
    by simp only [single_eq_C_mul_X.symm]; exact degree_sum_le _ _
  ... ≤ p.support.sup (λi, q.support.sup (λj, degree (C (coeff p i * coeff q j) * X ^ (i + j)))) :
    finset.sup_mono_fun (assume i hi,  degree_sum_le _ _)
  ... ≤ degree p + degree q :
    begin
      refine finset.sup_le (λ a ha, finset.sup_le (λ b hb, le_trans (degree_monomial_le _ _) _)),
      rw [with_bot.coe_add],
      rw mem_support_iff at ha hb,
      exact add_le_add' (le_degree_of_ne_zero ha) (le_degree_of_ne_zero hb)
    end

lemma degree_pow_le (p : polynomial R) : ∀ n, degree (p ^ n) ≤ n •ℕ (degree p)
| 0     := by rw [pow_zero, zero_nsmul]; exact degree_one_le
| (n+1) := calc degree (p ^ (n + 1)) ≤ degree p + degree (p ^ n) :
    by rw pow_succ; exact degree_mul_le _ _
  ... ≤ _ : by rw succ_nsmul; exact add_le_add' (le_refl _) (degree_pow_le _)

@[simp] lemma leading_coeff_monomial (a : R) (n : ℕ) : leading_coeff (C a * X ^ n) = a :=
begin
  by_cases ha : a = 0,
  { simp only [ha, C_0, zero_mul, leading_coeff_zero] },
  { rw [leading_coeff, nat_degree, degree_monomial _ ha, ← single_eq_C_mul_X],
    exact @finsupp.single_eq_same _ _ _ n a }
end

@[simp] lemma leading_coeff_C (a : R) : leading_coeff (C a) = a :=
suffices leading_coeff (C a * X^0) = a, by rwa [pow_zero, mul_one] at this,
leading_coeff_monomial a 0

@[simp] lemma leading_coeff_X : leading_coeff (X : polynomial R) = 1 :=
suffices leading_coeff (C (1:R) * X^1) = 1, by rwa [C_1, pow_one, one_mul] at this,
leading_coeff_monomial 1 1

@[simp] lemma monic_X : monic (X : polynomial R) := leading_coeff_X

@[simp] lemma leading_coeff_one : leading_coeff (1 : polynomial R) = 1 :=
suffices leading_coeff (C (1:R) * X^0) = 1, by rwa [C_1, pow_zero, mul_one] at this,
leading_coeff_monomial 1 0

@[simp] lemma monic_one : monic (1 : polynomial R) := leading_coeff_C _

lemma monic.ne_zero_of_zero_ne_one (h : (0:R) ≠ 1) {p : polynomial R} (hp : p.monic) :
  p ≠ 0 :=
by { contrapose! h, rwa [h] at hp }

lemma monic.ne_zero {R : Type*} [comm_semiring R] [nonzero R] {p : polynomial R} (hp : p.monic) :
  p ≠ 0 :=
hp.ne_zero_of_zero_ne_one zero_ne_one

lemma leading_coeff_add_of_degree_lt (h : degree p < degree q) :
  leading_coeff (p + q) = leading_coeff q :=
have coeff p (nat_degree q) = 0, from coeff_nat_degree_eq_zero_of_degree_lt h,
by simp only [leading_coeff, nat_degree_eq_of_degree_eq (degree_add_eq_of_degree_lt h),
  this, coeff_add, zero_add]

lemma leading_coeff_add_of_degree_eq (h : degree p = degree q)
  (hlc : leading_coeff p + leading_coeff q ≠ 0) :
  leading_coeff (p + q) = leading_coeff p + leading_coeff q :=
have nat_degree (p + q) = nat_degree p,
  by apply nat_degree_eq_of_degree_eq;
    rw [degree_add_eq_of_leading_coeff_add_ne_zero hlc, h, max_self],
by simp only [leading_coeff, this, nat_degree_eq_of_degree_eq h, coeff_add]

@[simp] lemma coeff_mul_degree_add_degree (p q : polynomial R) :
  coeff (p * q) (nat_degree p + nat_degree q) = leading_coeff p * leading_coeff q :=
calc coeff (p * q) (nat_degree p + nat_degree q) =
    (nat.antidiagonal (nat_degree p + nat_degree q)).sum
    (λ x, coeff p x.1 * coeff q x.2) : coeff_mul _ _ _
... = coeff p (nat_degree p) * coeff q (nat_degree q) :
  begin
    refine finset.sum_eq_single (nat_degree p, nat_degree q) _ _,
    { rintro ⟨i,j⟩ h₁ h₂, rw nat.mem_antidiagonal at h₁,
      by_cases H : nat_degree p < i,
      { rw [coeff_eq_zero_of_degree_lt
          (lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 H)), zero_mul] },
      { rw not_lt_iff_eq_or_lt at H, cases H,
        { subst H, rw add_left_cancel_iff at h₁, dsimp at h₁, subst h₁, exfalso, exact h₂ rfl },
        { suffices : nat_degree q < j,
          { rw [coeff_eq_zero_of_degree_lt
              (lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 this)), mul_zero] },
          { by_contra H', rw not_lt at H',
            exact ne_of_lt (nat.lt_of_lt_of_le
              (nat.add_lt_add_right H j) (nat.add_le_add_left H' _)) h₁ } } } },
    { intro H, exfalso, apply H, rw nat.mem_antidiagonal }
  end

lemma degree_mul_eq' (h : leading_coeff p * leading_coeff q ≠ 0) :
  degree (p * q) = degree p + degree q :=
have hp : p ≠ 0 := by refine mt _ h; exact λ hp, by rw [hp, leading_coeff_zero, zero_mul],
have hq : q ≠ 0 := by refine mt _ h; exact λ hq, by rw [hq, leading_coeff_zero, mul_zero],
le_antisymm (degree_mul_le _ _)
begin
  rw [degree_eq_nat_degree hp, degree_eq_nat_degree hq],
  refine le_degree_of_ne_zero _,
  rwa coeff_mul_degree_add_degree
end

lemma nat_degree_mul_eq' (h : leading_coeff p * leading_coeff q ≠ 0) :
  nat_degree (p * q) = nat_degree p + nat_degree q :=
have hp : p ≠ 0 := mt leading_coeff_eq_zero.2 (λ h₁, h $ by rw [h₁, zero_mul]),
have hq : q ≠ 0 := mt leading_coeff_eq_zero.2 (λ h₁, h $ by rw [h₁, mul_zero]),
have hpq : p * q ≠ 0 := λ hpq, by rw [← coeff_mul_degree_add_degree, hpq, coeff_zero] at h;
  exact h rfl,
option.some_inj.1 (show (nat_degree (p * q) : with_bot ℕ) = nat_degree p + nat_degree q,
  by rw [← degree_eq_nat_degree hpq, degree_mul_eq' h, degree_eq_nat_degree hp,
    degree_eq_nat_degree hq])

lemma leading_coeff_mul' (h : leading_coeff p * leading_coeff q ≠ 0) :
  leading_coeff (p * q) = leading_coeff p * leading_coeff q :=
begin
  unfold leading_coeff,
  rw [nat_degree_mul_eq' h, coeff_mul_degree_add_degree],
  refl
end

lemma leading_coeff_pow' : leading_coeff p ^ n ≠ 0 →
  leading_coeff (p ^ n) = leading_coeff p ^ n :=
nat.rec_on n (by simp) $
λ n ih h,
have h₁ : leading_coeff p ^ n ≠ 0 :=
  λ h₁, h $ by rw [pow_succ, h₁, mul_zero],
have h₂ : leading_coeff p * leading_coeff (p ^ n) ≠ 0 :=
  by rwa [pow_succ, ← ih h₁] at h,
by rw [pow_succ, pow_succ, leading_coeff_mul' h₂, ih h₁]

lemma degree_pow_eq' : ∀ {n}, leading_coeff p ^ n ≠ 0 →
  degree (p ^ n) = n •ℕ (degree p)
| 0     := λ h, by rw [pow_zero, ← C_1] at *;
  rw [degree_C h, zero_nsmul]
| (n+1) := λ h,
have h₁ : leading_coeff p ^ n ≠ 0 := λ h₁, h $
  by rw [pow_succ, h₁, mul_zero],
have h₂ : leading_coeff p * leading_coeff (p ^ n) ≠ 0 :=
  by rwa [pow_succ, ← leading_coeff_pow' h₁] at h,
by rw [pow_succ, degree_mul_eq' h₂, succ_nsmul, degree_pow_eq' h₁]

lemma nat_degree_pow_eq' {n : ℕ} (h : leading_coeff p ^ n ≠ 0) :
  nat_degree (p ^ n) = n * nat_degree p :=
if hp0 : p = 0 then
  if hn0 : n = 0 then by simp *
  else by rw [hp0, zero_pow (nat.pos_of_ne_zero hn0)]; simp
else
have hpn : p ^ n ≠ 0, from λ hpn0,  have h1 : _ := h,
  by rw [← leading_coeff_pow' h1, hpn0, leading_coeff_zero] at h;
  exact h rfl,
option.some_inj.1 $ show (nat_degree (p ^ n) : with_bot ℕ) = (n * nat_degree p : ℕ),
  by rw [← degree_eq_nat_degree hpn, degree_pow_eq' h, degree_eq_nat_degree hp0,
    ← with_bot.coe_nsmul]; simp

@[simp] lemma leading_coeff_X_pow : ∀ n : ℕ, leading_coeff ((X : polynomial R) ^ n) = 1
| 0 := by simp
| (n+1) :=
if h10 : (1 : R) = 0
then by rw [pow_succ, ← one_mul X, ← C_1, h10]; simp
else
have h : leading_coeff (X : polynomial R) * leading_coeff (X ^ n) ≠ 0,
  by rw [leading_coeff_X, leading_coeff_X_pow n, one_mul];
    exact h10,
by rw [pow_succ, leading_coeff_mul' h, leading_coeff_X, leading_coeff_X_pow, one_mul]

lemma nat_degree_comp_le : nat_degree (p.comp q) ≤ nat_degree p * nat_degree q :=
if h0 : p.comp q = 0 then by rw [h0, nat_degree_zero]; exact nat.zero_le _
else with_bot.coe_le_coe.1 $
  calc ↑(nat_degree (p.comp q)) = degree (p.comp q) : (degree_eq_nat_degree h0).symm
  ... ≤ _ : degree_sum_le _ _
  ... ≤ _ : sup_le (λ n hn,
    calc degree (C (coeff p n) * q ^ n)
        ≤ degree (C (coeff p n)) + degree (q ^ n) : degree_mul_le _ _
    ... ≤ nat_degree (C (coeff p n)) + n •ℕ (degree q) :
      add_le_add' degree_le_nat_degree (degree_pow_le _ _)
    ... ≤ nat_degree (C (coeff p n)) + n •ℕ (nat_degree q) :
      add_le_add_left' (nsmul_le_nsmul_of_le_right (@degree_le_nat_degree _ _ q) n)
    ... = (n * nat_degree q : ℕ) :
     by rw [nat_degree_C, with_bot.coe_zero, zero_add, ← with_bot.coe_nsmul,
       nsmul_eq_mul]; simp
    ... ≤ (nat_degree p * nat_degree q : ℕ) : with_bot.coe_le_coe.2 $
      mul_le_mul_of_nonneg_right
        (le_nat_degree_of_ne_zero (finsupp.mem_support_iff.1 hn))
        (nat.zero_le _))

lemma degree_map_le [comm_semiring S] (f : R →+* S) :
  degree (p.map f) ≤ degree p :=
if h : p.map f = 0 then by simp [h]
else begin
  rw [degree_eq_nat_degree h],
  refine le_degree_of_ne_zero (mt (congr_arg f) _),
  rw [← coeff_map f, is_semiring_hom.map_zero f],
  exact mt leading_coeff_eq_zero.1 h
end

lemma subsingleton_of_monic_zero (h : monic (0 : polynomial R)) :
  (∀ p q : polynomial R, p = q) ∧ (∀ a b : R, a = b) :=
by rw [monic.def, leading_coeff_zero] at h;
  exact ⟨λ p q, by rw [← mul_one p, ← mul_one q, ← C_1, ← h, C_0, mul_zero, mul_zero],
    λ a b, by rw [← mul_one a, ← mul_one b, ← h, mul_zero, mul_zero]⟩

lemma degree_map_eq_of_leading_coeff_ne_zero [comm_semiring S] (f : R →+* S)
  (hf : f (leading_coeff p) ≠ 0) : degree (p.map f) = degree p :=
le_antisymm (degree_map_le f) $
  have hp0 : p ≠ 0, from λ hp0, by simpa [hp0, is_semiring_hom.map_zero f] using hf,
  begin
    rw [degree_eq_nat_degree hp0],
    refine le_degree_of_ne_zero _,
    rw [coeff_map], exact hf
  end

lemma monic_map [comm_semiring S] (f : R →+* S) (hp : monic p) : monic (p.map f) :=
if h : (0 : S) = 1 then
  by haveI := subsingleton_of_zero_eq_one S h;
  exact subsingleton.elim _ _
else
have f (leading_coeff p) ≠ 0,
  by rwa [show _ = _, from hp, is_semiring_hom.map_one f, ne.def, eq_comm],
by erw [monic, leading_coeff, nat_degree_eq_of_degree_eq
    (degree_map_eq_of_leading_coeff_ne_zero f this), coeff_map,
    ← leading_coeff, show _ = _, from hp, is_semiring_hom.map_one f]

lemma zero_le_degree_iff {p : polynomial R} : 0 ≤ degree p ↔ p ≠ 0 :=
by rw [ne.def, ← degree_eq_bot];
  cases degree p; exact dec_trivial

@[simp] lemma coeff_mul_X_zero (p : polynomial R) : coeff (p * X) 0 = 0 :=
by rw [coeff_mul, nat.antidiagonal_zero];
simp only [polynomial.coeff_X_zero, finset.sum_singleton, mul_zero]

lemma is_unit_C {x : R} : is_unit (C x) ↔ is_unit x :=
begin
  rw [is_unit_iff_dvd_one, is_unit_iff_dvd_one],
  split,
  { rintros ⟨g, hg⟩,
    replace hg := congr_arg (eval 0) hg,
    rw [eval_one, eval_mul, eval_C] at hg,
    exact ⟨g.eval 0, hg⟩ },
  { rintros ⟨y, hy⟩,
    exact ⟨C y, by rw [← C_mul, ← hy, C_1]⟩ }
end

lemma degree_nonneg_iff_ne_zero : 0 ≤ degree p ↔ p ≠ 0 :=
⟨λ h0p hp0, absurd h0p (by rw [hp0, degree_zero]; exact dec_trivial),
  λ hp0, le_of_not_gt (λ h, by simp [gt, degree_eq_bot, *] at *)⟩

lemma nat_degree_eq_zero_iff_degree_le_zero : p.nat_degree = 0 ↔ p.degree ≤ 0 :=
if hp0 : p = 0 then by simp [hp0]
else by rw [degree_eq_nat_degree hp0, ← with_bot.coe_zero, with_bot.coe_le_coe,
  nat.le_zero_iff]

lemma eq_one_of_is_unit_of_monic (hm : monic p) (hpu : is_unit p) : p = 1 :=
have degree p ≤ 0,
  from calc degree p ≤ degree (1 : polynomial R) :
    let ⟨u, hu⟩ := is_unit_iff_dvd_one.1 hpu in
    if hu0 : u = 0
    then begin
        rw [hu0, mul_zero] at hu,
        rw [← mul_one p, hu, mul_zero],
        simp
      end
    else have p.leading_coeff * u.leading_coeff ≠ 0,
        by rw [hm.leading_coeff, one_mul, ne.def, leading_coeff_eq_zero];
          exact hu0,
      by rw [hu, degree_mul_eq' this];
        exact le_add_of_nonneg_right' (degree_nonneg_iff_ne_zero.2 hu0)
  ... ≤ 0 : degree_one_le,
by rw [eq_C_of_degree_le_zero this, ← nat_degree_eq_zero_iff_degree_le_zero.2 this,
    ← leading_coeff, hm.leading_coeff, C_1]

end comm_semiring

instance subsingleton [subsingleton R] [comm_semiring R] : subsingleton (polynomial R) :=
⟨λ _ _, ext (λ _, subsingleton.elim _ _)⟩

section comm_semiring

variables [comm_semiring R] {p q r : polynomial R}

lemma ne_zero_of_monic_of_zero_ne_one (hp : monic p) (h : (0 : R) ≠ 1) :
  p ≠ 0 := mt (congr_arg leading_coeff) $ by rw [monic.def.1 hp, leading_coeff_zero]; cc

lemma eq_X_add_C_of_degree_le_one (h : degree p ≤ 1) :
  p = C (p.coeff 1) * X + C (p.coeff 0) :=
ext (λ n, nat.cases_on n (by simp)
  (λ n, nat.cases_on n (by simp [coeff_C])
    (λ m, have degree p < m.succ.succ, from lt_of_le_of_lt h dec_trivial,
      by simp [coeff_eq_zero_of_degree_lt this, coeff_C, nat.succ_ne_zero, coeff_X,
        nat.succ_inj', @eq_comm ℕ 0])))

lemma eq_X_add_C_of_degree_eq_one (h : degree p = 1) :
  p = C (p.leading_coeff) * X + C (p.coeff 0) :=
(eq_X_add_C_of_degree_le_one (show degree p ≤ 1, from h ▸ le_refl _)).trans
  (by simp [leading_coeff, nat_degree_eq_of_degree_eq_some h])

theorem degree_C_mul_X_pow_le (r : R) (n : ℕ) : degree (C r * X^n) ≤ n :=
begin
  rw [← single_eq_C_mul_X],
  refine finset.sup_le (λ b hb, _),
  rw list.eq_of_mem_singleton (finsupp.support_single_subset hb),
  exact le_refl _
end

theorem degree_X_pow_le (n : ℕ) : degree (X^n : polynomial R) ≤ n :=
by simpa only [C_1, one_mul] using degree_C_mul_X_pow_le (1:R) n

theorem degree_X_le : degree (X : polynomial R) ≤ 1 :=
by simpa only [C_1, one_mul, pow_one] using degree_C_mul_X_pow_le (1:R) 1

section injective
open function
variables [comm_semiring S] {f : R →+* S} (hf : function.injective f)
include hf

lemma degree_map_eq_of_injective (p : polynomial R) : degree (p.map f) = degree p :=
if h : p = 0 then by simp [h]
else degree_map_eq_of_leading_coeff_ne_zero _
  (by rw [← is_semiring_hom.map_zero f]; exact mt hf.eq_iff.1
    (mt leading_coeff_eq_zero.1 h))

lemma degree_map' (p : polynomial R) :
  degree (p.map f) = degree p :=
p.degree_map_eq_of_injective hf

lemma nat_degree_map' (p : polynomial R) :
  nat_degree (p.map f) = nat_degree p :=
nat_degree_eq_of_degree_eq (degree_map' hf p)

lemma map_injective : injective (map f) :=
λ p q h, ext $ λ m, hf $
begin
  rw ext_iff at h,
  specialize h m,
  rw [coeff_map f, coeff_map f] at h,
  exact h
end

lemma leading_coeff_of_injective (p : polynomial R) :
  leading_coeff (p.map f) = f (leading_coeff p) :=
begin
  delta leading_coeff,
  rw [coeff_map f, nat_degree_map' hf p]
end

lemma monic_of_injective {p : polynomial R} (hp : (p.map f).monic) : p.monic :=
begin
  apply hf,
  rw [← leading_coeff_of_injective hf, hp.leading_coeff, is_semiring_hom.map_one f]
end

end injective

theorem monic_of_degree_le (n : ℕ) (H1 : degree p ≤ n) (H2 : coeff p n = 1) : monic p :=
decidable.by_cases
  (assume H : degree p < n, @subsingleton.elim _ (subsingleton_of_zero_eq_one R $
    H2 ▸ (coeff_eq_zero_of_degree_lt H).symm) _ _)
  (assume H : ¬degree p < n,
    by rwa [monic, leading_coeff, nat_degree, (lt_or_eq_of_le H1).resolve_left H])

theorem monic_X_pow_add {n : ℕ} (H : degree p ≤ n) : monic (X ^ (n+1) + p) :=
have H1 : degree p < n+1, from lt_of_le_of_lt H (with_bot.coe_lt_coe.2 (nat.lt_succ_self n)),
monic_of_degree_le (n+1)
  (le_trans (degree_add_le _ _) (max_le (degree_X_pow_le _) (le_of_lt H1)))
  (by rw [coeff_add, coeff_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt H1, add_zero])

theorem monic_X_add_C (x : R) : monic (X + C x) :=
pow_one (X : polynomial R) ▸ monic_X_pow_add degree_C_le

theorem degree_le_iff_coeff_zero (f : polynomial R) (n : with_bot ℕ) :
  degree f ≤ n ↔ ∀ m : ℕ, n < m → coeff f m = 0 :=
⟨λ (H : finset.sup (f.support) some ≤ n) m (Hm : n < (m : with_bot ℕ)), decidable.of_not_not $ λ H4,
  have H1 : m ∉ f.support,
    from λ H2, not_lt_of_ge ((finset.sup_le_iff.1 H) m H2 : ((m : with_bot ℕ) ≤ n)) Hm,
  H1 $ (finsupp.mem_support_to_fun f m).2 H4,
λ H, finset.sup_le $ λ b Hb, decidable.of_not_not $ λ Hn,
  (finsupp.mem_support_to_fun f b).1 Hb $ H b $ lt_of_not_ge Hn⟩

theorem nat_degree_le_of_degree_le {p : polynomial R} {n : ℕ}
  (H : degree p ≤ n) : nat_degree p ≤ n :=
show option.get_or_else (degree p) 0 ≤ n, from match degree p, H with
| none,     H := zero_le _
| (some d), H := with_bot.coe_le_coe.1 H
end

theorem leading_coeff_mul_X_pow {p : polynomial R} {n : ℕ} :
  leading_coeff (p * X ^ n) = leading_coeff p :=
decidable.by_cases
  (λ H : leading_coeff p = 0, by rw [H, leading_coeff_eq_zero.1 H, zero_mul, leading_coeff_zero])
  (λ H : leading_coeff p ≠ 0,
    by rw [leading_coeff_mul', leading_coeff_X_pow, mul_one];
      rwa [leading_coeff_X_pow, mul_one])

lemma monic_mul (hp : monic p) (hq : monic q) : monic (p * q) :=
if h0 : (0 : R) = 1 then by haveI := subsingleton_of_zero_eq_one _ h0;
  exact subsingleton.elim _ _
else
  have leading_coeff p * leading_coeff q ≠ 0, by simp [monic.def.1 hp, monic.def.1 hq, ne.symm h0],
  by rw [monic.def, leading_coeff_mul' this, monic.def.1 hp, monic.def.1 hq, one_mul]

lemma monic_pow (hp : monic p) : ∀ (n : ℕ), monic (p ^ n)
| 0     := monic_one
| (n+1) := monic_mul hp (monic_pow n)

lemma multiplicity_finite_of_degree_pos_of_monic (hp : (0 : with_bot ℕ) < degree p)
  (hmp : monic p) (hq : q ≠ 0) : multiplicity.finite p q :=
have zn0 : (0 : R) ≠ 1, from λ h, by haveI := subsingleton_of_zero_eq_one _ h;
  exact hq (subsingleton.elim _ _),
⟨nat_degree q, λ ⟨r, hr⟩,
  have hp0 : p ≠ 0, from λ hp0, by simp [hp0] at hp; contradiction,
  have hr0 : r ≠ 0, from λ hr0, by simp * at *,
  have hpn1 : leading_coeff p ^ (nat_degree q + 1) = 1,
    by simp [show _ = _, from hmp],
  have hpn0' : leading_coeff p ^ (nat_degree q + 1) ≠ 0,
    from hpn1.symm ▸ zn0.symm,
  have hpnr0 : leading_coeff (p ^ (nat_degree q + 1)) * leading_coeff r ≠ 0,
    by simp only [leading_coeff_pow' hpn0', leading_coeff_eq_zero, hpn1,
      one_pow, one_mul, ne.def, hr0]; simp,
  have hpn0 : p ^ (nat_degree q + 1) ≠ 0,
    from mt leading_coeff_eq_zero.2 $
      by rw [leading_coeff_pow' hpn0', show _ = _, from hmp, one_pow]; exact zn0.symm,
  have hnp : 0 < nat_degree p,
    by rw [← with_bot.coe_lt_coe, ← degree_eq_nat_degree hp0];
    exact hp,
  begin
    have := congr_arg nat_degree hr,
    rw [nat_degree_mul_eq' hpnr0,  nat_degree_pow_eq' hpn0', add_mul, add_assoc] at this,
    exact ne_of_lt (lt_add_of_le_of_pos (le_mul_of_one_le_right' (nat.zero_le _) hnp)
      (add_pos_of_pos_of_nonneg (by rwa one_mul) (nat.zero_le _))) this
  end⟩

end comm_semiring

section nonzero_comm_semiring
variables [comm_semiring R] [nonzero R] {p q : polynomial R}

instance : nonzero (polynomial R) :=
{ zero_ne_one := λ (h : (0 : polynomial R) = 1), zero_ne_one $
    calc (0 : R) = eval 0 0 : eval_zero.symm
      ... = eval 0 1 : congr_arg _ h
      ... = 1 : eval_C }

@[simp] lemma degree_one : degree (1 : polynomial R) = (0 : with_bot ℕ) :=
degree_C (show (1 : R) ≠ 0, from zero_ne_one.symm)

@[simp] lemma degree_X : degree (X : polynomial R) = 1 :=
begin
  unfold X degree monomial single finsupp.support,
  rw if_neg (one_ne_zero : (1 : R) ≠ 0),
  refl
end

lemma X_ne_zero : (X : polynomial R) ≠ 0 :=
mt (congr_arg (λ p, coeff p 1)) (by simp)

@[simp] lemma degree_X_pow : ∀ (n : ℕ), degree ((X : polynomial R) ^ n) = n
| 0 := by simp only [pow_zero, degree_one]; refl
| (n+1) :=
have h : leading_coeff (X : polynomial R) * leading_coeff (X ^ n) ≠ 0,
  by rw [leading_coeff_X, leading_coeff_X_pow n, one_mul];
    exact zero_ne_one.symm,
by rw [pow_succ, degree_mul_eq' h, degree_X, degree_X_pow, add_comm]; refl

@[simp] lemma not_monic_zero : ¬monic (0 : polynomial R) :=
by simpa only [monic, leading_coeff_zero] using (zero_ne_one : (0 : R) ≠ 1)

lemma ne_zero_of_monic (h : monic p) : p ≠ 0 :=
λ h₁, @not_monic_zero R _ _ (h₁ ▸ h)

end nonzero_comm_semiring

section comm_semiring
variables [comm_semiring R] {p q : polynomial R}

/-- `dix_X p` return a polynomial `q` such that `q * X + C (p.coeff 0) = p`.
  It can be used in a semiring where the usual division algorithm is not possible -/
def div_X (p : polynomial R) : polynomial R :=
{ to_fun := λ n, p.coeff (n + 1),
  support := ⟨(p.support.filter (> 0)).1.map (λ n, n - 1),
    multiset.nodup_map_on begin
        simp only [finset.mem_def.symm, finset.mem_erase, finset.mem_filter],
        assume x hx y hy hxy,
        rwa [← @add_right_cancel_iff _ _ 1, nat.sub_add_cancel hx.2,
          nat.sub_add_cancel hy.2] at hxy
      end
      (p.support.filter (> 0)).2⟩,
  mem_support_to_fun := λ n,
    suffices (∃ (a : ℕ), (¬coeff p a = 0 ∧ a > 0) ∧ a - 1 = n) ↔
      ¬coeff p (n + 1) = 0,
    by simpa [finset.mem_def.symm, apply_eq_coeff],
    ⟨λ ⟨a, ha⟩, by rw [← ha.2, nat.sub_add_cancel ha.1.2]; exact ha.1.1,
      λ h, ⟨n + 1, ⟨h, nat.succ_pos _⟩, nat.succ_sub_one _⟩⟩ }

lemma div_X_mul_X_add (p : polynomial R) : div_X p * X + C (p.coeff 0) = p :=
ext $ λ n,
  nat.cases_on n
   (by simp)
   (by simp [coeff_C, nat.succ_ne_zero, coeff_mul_X, div_X])

@[simp] lemma div_X_C (a : R) : div_X (C a) = 0 :=
ext $ λ n, by cases n; simp [div_X, coeff_C]; simp [coeff]

lemma div_X_eq_zero_iff : div_X p = 0 ↔ p = C (p.coeff 0) :=
⟨λ h, by simpa [eq_comm, h] using div_X_mul_X_add p,
  λ h, by rw [h, div_X_C]⟩

lemma div_X_add : div_X (p + q) = div_X p + div_X q :=
ext $ by simp [div_X]

theorem nonzero.of_polynomial_ne (h : p ≠ q) : nonzero R :=
{ zero_ne_one := λ h01 : 0 = 1, h $
    by rw [← mul_one p, ← mul_one q, ← C_1, ← h01, C_0, mul_zero, mul_zero] }

lemma degree_lt_degree_mul_X (hp : p ≠ 0) : p.degree < (p * X).degree :=
by haveI := nonzero.of_polynomial_ne hp; exact
have leading_coeff p * leading_coeff X ≠ 0, by simpa,
by erw [degree_mul_eq' this, degree_eq_nat_degree hp,
    degree_X, ← with_bot.coe_one, ← with_bot.coe_add, with_bot.coe_lt_coe];
  exact nat.lt_succ_self _

lemma degree_div_X_lt (hp0 : p ≠ 0) : (div_X p).degree < p.degree :=
by haveI := nonzero.of_polynomial_ne hp0; exact
calc (div_X p).degree < (div_X p * X + C (p.coeff 0)).degree :
  if h : degree p ≤ 0
  then begin
      have h' : C (p.coeff 0) ≠ 0, by rwa [← eq_C_of_degree_le_zero h],
      rw [eq_C_of_degree_le_zero h, div_X_C, degree_zero, zero_mul, zero_add],
      exact lt_of_le_of_ne bot_le (ne.symm (mt degree_eq_bot.1 $
        by simp [h'])),
    end
  else
    have hXp0 : div_X p ≠ 0,
      by simpa [div_X_eq_zero_iff, -not_le, degree_le_zero_iff] using h,
    have leading_coeff (div_X p) * leading_coeff X ≠ 0, by simpa,
    have degree (C (p.coeff 0)) < degree (div_X p * X),
      from calc degree (C (p.coeff 0)) ≤ 0 : degree_C_le
         ... < 1 : dec_trivial
         ... = degree (X : polynomial R) : degree_X.symm
         ... ≤ degree (div_X p * X) :
          by rw [← zero_add (degree X), degree_mul_eq' this];
            exact add_le_add'
              (by rw [zero_le_degree_iff, ne.def, div_X_eq_zero_iff];
                exact λ h0, h (h0.symm ▸ degree_C_le))
              (le_refl _),
    by rw [add_comm, degree_add_eq_of_degree_lt this];
      exact degree_lt_degree_mul_X hXp0
... = p.degree : by rw div_X_mul_X_add

@[elab_as_eliminator] noncomputable def rec_on_horner
  {M : polynomial R → Sort*} : Π (p : polynomial R),
  M 0 →
  (Π p a, coeff p 0 = 0 → a ≠ 0 → M p → M (p + C a)) →
  (Π p, p ≠ 0 → M p → M (p * X)) →
  M p
| p := λ M0 MC MX,
if hp : p = 0 then eq.rec_on hp.symm M0
else
have wf : degree (div_X p) < degree p,
  from degree_div_X_lt hp,
by rw [← div_X_mul_X_add p] at *;
  exact
  if hcp0 : coeff p 0 = 0
  then by rw [hcp0, C_0, add_zero];
    exact MX _ (λ h : div_X p = 0, by simpa [h, hcp0] using hp)
      (rec_on_horner _ M0 MC MX)
  else MC _ _ (coeff_mul_X_zero _) hcp0 (if hpX0 : div_X p = 0
    then show M (div_X p * X), by rw [hpX0, zero_mul]; exact M0
    else MX (div_X p) hpX0 (rec_on_horner _ M0 MC MX))
using_well_founded {dec_tac := tactic.assumption}

@[elab_as_eliminator] lemma degree_pos_induction_on
  {P : polynomial R → Prop} (p : polynomial R) (h0 : 0 < degree p)
  (hC : ∀ {a}, a ≠ 0 → P (C a * X))
  (hX : ∀ {p}, 0 < degree p → P p → P (p * X))
  (hadd : ∀ {p} {a}, 0 < degree p → P p → P (p + C a)) : P p :=
rec_on_horner p
  (λ h, by rw degree_zero at h; exact absurd h dec_trivial)
  (λ p a _ _ ih h0,
    have 0 < degree p,
      from lt_of_not_ge (λ h, (not_lt_of_ge degree_C_le) $
        by rwa [eq_C_of_degree_le_zero h, ← C_add] at h0),
    hadd this (ih this))
  (λ p _ ih h0',
    if h0 : 0 < degree p
    then hX h0 (ih h0)
    else by rw [eq_C_of_degree_le_zero (le_of_not_gt h0)] at *;
      exact hC (λ h : coeff p 0 = 0,
        by simpa [h, nat.not_lt_zero] using h0'))
  h0

end comm_semiring

section comm_ring
variables [comm_ring R] {p q : polynomial R}
instance : comm_ring (polynomial R) := monoid_algebra.comm_ring
instance : module R (polynomial R) := monoid_algebra.module

variable (R)
def lcoeff (n : ℕ) : polynomial R →ₗ R :=
{ to_fun := λ f, coeff f n,
  add := λ f g, coeff_add f g n,
  smul := λ r p, coeff_smul p r n }
variable {R}

@[simp] lemma lcoeff_apply (n : ℕ) (f : polynomial R) : lcoeff R n f = coeff f n := rfl

instance C.is_ring_hom : is_ring_hom (@C R _) := by apply is_ring_hom.of_semiring

lemma int_cast_eq_C (n : ℤ) : (n : polynomial R) = C n :=
((ring_hom.of C).map_int_cast n).symm

@[simp] lemma C_neg : C (-a) = -C a := is_ring_hom.map_neg C

@[simp] lemma C_sub : C (a - b) = C a - C b := is_ring_hom.map_sub C

instance eval₂.is_ring_hom {S} [comm_ring S]
  (f : R → S) [is_ring_hom f] {x : S} : is_ring_hom (eval₂ f x) :=
by apply is_ring_hom.of_semiring

instance eval.is_ring_hom {x : R} : is_ring_hom (eval x) := eval₂.is_ring_hom _

instance map.is_ring_hom {S} [comm_ring S] (f : R →+* S) : is_ring_hom (map f) :=
eval₂.is_ring_hom (C ∘ f)

@[simp] lemma map_sub {S} [comm_ring S] (f : R →+* S) :
  (p - q).map f = p.map f - q.map f :=
is_ring_hom.map_sub _

@[simp] lemma map_neg {S} [comm_ring S] (f : R →+* S) :
  (-p).map f = -(p.map f) :=
is_ring_hom.map_neg _

@[simp] lemma degree_neg (p : polynomial R) : degree (-p) = degree p :=
by unfold degree; rw support_neg

lemma degree_sub_le (p q : polynomial R) : degree (p - q) ≤ max (degree p) (degree q) :=
degree_neg q ▸ degree_add_le p (-q)

@[simp] lemma nat_degree_neg (p : polynomial R) : nat_degree (-p) = nat_degree p :=
by simp [nat_degree]

@[simp] lemma nat_degree_int_cast (n : ℤ) : nat_degree (n : polynomial R) = 0 :=
by simp [int_cast_eq_C]

@[simp] lemma coeff_neg (p : polynomial R) (n : ℕ) : coeff (-p) n = -coeff p n := rfl

@[simp]
lemma coeff_sub (p q : polynomial R) (n : ℕ) : coeff (p - q) n = coeff p n - coeff q n := rfl

@[simp] lemma eval₂_neg {S} [comm_ring S] (f : R → S) [is_ring_hom f] {x : S} :
  (-p).eval₂ f x = -p.eval₂ f x :=
is_ring_hom.map_neg _

@[simp] lemma eval₂_sub {S} [comm_ring S] (f : R → S) [is_ring_hom f] {x : S} :
  (p - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x :=
is_ring_hom.map_sub _

@[simp] lemma eval_neg (p : polynomial R) (x : R) : (-p).eval x = -p.eval x :=
is_ring_hom.map_neg _

@[simp] lemma eval_sub (p q : polynomial R) (x : R) : (p - q).eval x = p.eval x - q.eval x :=
is_ring_hom.map_sub _

lemma degree_sub_lt (hd : degree p = degree q)
  (hp0 : p ≠ 0) (hlc : leading_coeff p = leading_coeff q) :
  degree (p - q) < degree p :=
have hp : single (nat_degree p) (leading_coeff p) + p.erase (nat_degree p) = p :=
  finsupp.single_add_erase,
have hq : single (nat_degree q) (leading_coeff q) + q.erase (nat_degree q) = q :=
  finsupp.single_add_erase,
have hd' : nat_degree p = nat_degree q := by unfold nat_degree; rw hd,
have hq0 : q ≠ 0 := mt degree_eq_bot.2 (hd ▸ mt degree_eq_bot.1 hp0),
calc degree (p - q) = degree (erase (nat_degree q) p + -erase (nat_degree q) q) :
  by conv {to_lhs, rw [← hp, ← hq, hlc, hd', add_sub_add_left_eq_sub, sub_eq_add_neg]}
... ≤ max (degree (erase (nat_degree q) p)) (degree (erase (nat_degree q) q))
  : degree_neg (erase (nat_degree q) q) ▸ degree_add_le _ _
... < degree p : max_lt_iff.2 ⟨hd' ▸ degree_erase_lt hp0, hd.symm ▸ degree_erase_lt hq0⟩

lemma ne_zero_of_ne_zero_of_monic (hp : p ≠ 0) (hq : monic q) : q ≠ 0
| h := begin
  rw [h, monic.def, leading_coeff_zero] at hq,
  rw [← mul_one p, ← C_1, ← hq, C_0, mul_zero] at hp,
  exact hp rfl
end

lemma div_wf_lemma (h : degree q ≤ degree p ∧ p ≠ 0) (hq : monic q) :
  degree (p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q) < degree p :=
have hp : leading_coeff p ≠ 0 := mt leading_coeff_eq_zero.1 h.2,
have hpq : leading_coeff (C (leading_coeff p) * X ^ (nat_degree p - nat_degree q)) *
    leading_coeff q ≠ 0,
  by rwa [leading_coeff_monomial, monic.def.1 hq, mul_one],
if h0 : p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q = 0
then h0.symm ▸ (lt_of_not_ge $ mt le_bot_iff.1 (mt degree_eq_bot.1 h.2))
else
  have hq0 : q ≠ 0 := ne_zero_of_ne_zero_of_monic h.2 hq,
  have hlt : nat_degree q ≤ nat_degree p := with_bot.coe_le_coe.1
    (by rw [← degree_eq_nat_degree h.2, ← degree_eq_nat_degree hq0];
    exact h.1),
  degree_sub_lt
  (by rw [degree_mul_eq' hpq, degree_monomial _ hp, degree_eq_nat_degree h.2,
      degree_eq_nat_degree hq0, ← with_bot.coe_add, nat.sub_add_cancel hlt])
  h.2
  (by rw [leading_coeff_mul' hpq, leading_coeff_monomial, monic.def.1 hq, mul_one])

noncomputable def div_mod_by_monic_aux : Π (p : polynomial R) {q : polynomial R},
  monic q → polynomial R × polynomial R
| p := λ q hq, if h : degree q ≤ degree p ∧ p ≠ 0 then
  let z := C (leading_coeff p) * X^(nat_degree p - nat_degree q)  in
  have wf : _ := div_wf_lemma h hq,
  let dm := div_mod_by_monic_aux (p - z * q) hq in
  ⟨z + dm.1, dm.2⟩
  else ⟨0, p⟩
using_well_founded {dec_tac := tactic.assumption}

/-- `div_by_monic` gives the quotient of `p` by a monic polynomial `q`. -/
def div_by_monic (p q : polynomial R) : polynomial R :=
if hq : monic q then (div_mod_by_monic_aux p hq).1 else 0

/-- `mod_by_monic` gives the remainder of `p` by a monic polynomial `q`. -/
def mod_by_monic (p q : polynomial R) : polynomial R :=
if hq : monic q then (div_mod_by_monic_aux p hq).2 else p

infixl  ` /ₘ ` : 70 := div_by_monic

infixl ` %ₘ ` : 70 := mod_by_monic

lemma degree_mod_by_monic_lt : ∀ (p : polynomial R) {q : polynomial R} (hq : monic q)
  (hq0 : q ≠ 0), degree (p %ₘ q) < degree q
| p := λ q hq hq0,
if h : degree q ≤ degree p ∧ p ≠ 0 then
  have wf : _ := div_wf_lemma ⟨h.1, h.2⟩ hq,
  have degree ((p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q) %ₘ q) < degree q :=
      degree_mod_by_monic_lt (p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q)
      hq hq0,
  begin
    unfold mod_by_monic at this ⊢,
    unfold div_mod_by_monic_aux,
    rw dif_pos hq at this ⊢,
    rw if_pos h,
    exact this
  end
else
  or.cases_on (not_and_distrib.1 h) begin
    unfold mod_by_monic div_mod_by_monic_aux,
    rw [dif_pos hq, if_neg h],
    exact lt_of_not_ge,
  end
  begin
    assume hp,
    unfold mod_by_monic div_mod_by_monic_aux,
    rw [dif_pos hq, if_neg h, not_not.1 hp],
    exact lt_of_le_of_ne bot_le
      (ne.symm (mt degree_eq_bot.1 hq0)),
  end
using_well_founded {dec_tac := tactic.assumption}

lemma mod_by_monic_eq_sub_mul_div : ∀ (p : polynomial R) {q : polynomial R} (hq : monic q),
  p %ₘ q = p - q * (p /ₘ q)
| p := λ q hq,
  if h : degree q ≤ degree p ∧ p ≠ 0 then
    have wf : _ := div_wf_lemma h hq,
    have ih : _ := mod_by_monic_eq_sub_mul_div
      (p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q) hq,
    begin
      unfold mod_by_monic div_by_monic div_mod_by_monic_aux,
      rw [dif_pos hq, if_pos h],
      rw [mod_by_monic, dif_pos hq] at ih,
      refine ih.trans _,
      unfold div_by_monic,
      rw [dif_pos hq, dif_pos hq, if_pos h, mul_add, sub_add_eq_sub_sub, mul_comm]
    end
  else
    begin
      unfold mod_by_monic div_by_monic div_mod_by_monic_aux,
      rw [dif_pos hq, if_neg h, dif_pos hq, if_neg h, mul_zero, sub_zero]
    end
using_well_founded {dec_tac := tactic.assumption}

lemma mod_by_monic_add_div (p : polynomial R) {q : polynomial R} (hq : monic q) :
  p %ₘ q + q * (p /ₘ q) = p := eq_sub_iff_add_eq.1 (mod_by_monic_eq_sub_mul_div p hq)

@[simp] lemma zero_mod_by_monic (p : polynomial R) : 0 %ₘ p = 0 :=
begin
  unfold mod_by_monic div_mod_by_monic_aux,
  by_cases hp : monic p,
  { rw [dif_pos hp, if_neg (mt and.right (not_not_intro rfl))] },
  { rw [dif_neg hp] }
end

@[simp] lemma zero_div_by_monic (p : polynomial R) : 0 /ₘ p = 0 :=
begin
  unfold div_by_monic div_mod_by_monic_aux,
  by_cases hp : monic p,
  { rw [dif_pos hp, if_neg (mt and.right (not_not_intro rfl))] },
  { rw [dif_neg hp] }
end

@[simp] lemma mod_by_monic_zero (p : polynomial R) : p %ₘ 0 = p :=
if h : monic (0 : polynomial R) then (subsingleton_of_monic_zero h).1 _ _ else
by unfold mod_by_monic div_mod_by_monic_aux; rw dif_neg h

@[simp] lemma div_by_monic_zero (p : polynomial R) : p /ₘ 0 = 0 :=
if h : monic (0 : polynomial R) then (subsingleton_of_monic_zero h).1 _ _ else
by unfold div_by_monic div_mod_by_monic_aux; rw dif_neg h

lemma div_by_monic_eq_of_not_monic (p : polynomial R) (hq : ¬monic q) : p /ₘ q = 0 := dif_neg hq

lemma mod_by_monic_eq_of_not_monic (p : polynomial R) (hq : ¬monic q) : p %ₘ q = p := dif_neg hq

lemma mod_by_monic_eq_self_iff (hq : monic q) (hq0 : q ≠ 0) : p %ₘ q = p ↔ degree p < degree q :=
⟨λ h, h ▸ degree_mod_by_monic_lt _ hq hq0,
λ h, have ¬ degree q ≤ degree p := not_le_of_gt h,
  by unfold mod_by_monic div_mod_by_monic_aux; rw [dif_pos hq, if_neg (mt and.left this)]⟩

lemma div_by_monic_eq_zero_iff (hq : monic q) (hq0 : q ≠ 0) : p /ₘ q = 0 ↔ degree p < degree q :=
⟨λ h, by have := mod_by_monic_add_div p hq;
  rwa [h, mul_zero, add_zero, mod_by_monic_eq_self_iff hq hq0] at this,
λ h, have ¬ degree q ≤ degree p := not_le_of_gt h,
  by unfold div_by_monic div_mod_by_monic_aux; rw [dif_pos hq, if_neg (mt and.left this)]⟩

lemma degree_add_div_by_monic (hq : monic q) (h : degree q ≤ degree p) :
  degree q + degree (p /ₘ q) = degree p :=
if hq0 : q = 0 then
  have ∀ (p : polynomial R), p = 0,
    from λ p, (@subsingleton_of_monic_zero R _ (hq0 ▸ hq)).1 _ _,
  by rw [this (p /ₘ q), this p, this q]; refl
else
have hdiv0 : p /ₘ q ≠ 0 := by rwa [(≠), div_by_monic_eq_zero_iff hq hq0, not_lt],
have hlc : leading_coeff q * leading_coeff (p /ₘ q) ≠ 0 :=
  by rwa [monic.def.1 hq, one_mul, (≠), leading_coeff_eq_zero],
have hmod : degree (p %ₘ q) < degree (q * (p /ₘ q)) :=
  calc degree (p %ₘ q) < degree q : degree_mod_by_monic_lt _ hq hq0
  ... ≤ _ : by rw [degree_mul_eq' hlc, degree_eq_nat_degree hq0,
      degree_eq_nat_degree hdiv0, ← with_bot.coe_add, with_bot.coe_le_coe];
    exact nat.le_add_right _ _,
calc degree q + degree (p /ₘ q) = degree (q * (p /ₘ q)) : eq.symm (degree_mul_eq' hlc)
... = degree (p %ₘ q + q * (p /ₘ q)) : (degree_add_eq_of_degree_lt hmod).symm
... = _ : congr_arg _ (mod_by_monic_add_div _ hq)

lemma degree_div_by_monic_le (p q : polynomial R) : degree (p /ₘ q) ≤ degree p :=
if hp0 : p = 0 then by simp only [hp0, zero_div_by_monic, le_refl]
else if hq : monic q then
  have hq0 : q ≠ 0 := ne_zero_of_ne_zero_of_monic hp0 hq,
  if h : degree q ≤ degree p
  then by rw [← degree_add_div_by_monic hq h, degree_eq_nat_degree hq0,
      degree_eq_nat_degree (mt (div_by_monic_eq_zero_iff hq hq0).1 (not_lt.2 h))];
    exact with_bot.coe_le_coe.2 (nat.le_add_left _ _)
  else
    by unfold div_by_monic div_mod_by_monic_aux;
      simp only [dif_pos hq, h, false_and, if_false, degree_zero, bot_le]
else (div_by_monic_eq_of_not_monic p hq).symm ▸ bot_le

lemma degree_div_by_monic_lt (p : polynomial R) {q : polynomial R} (hq : monic q)
  (hp0 : p ≠ 0) (h0q : 0 < degree q) : degree (p /ₘ q) < degree p :=
have hq0 : q ≠ 0 := ne_zero_of_ne_zero_of_monic hp0 hq,
if hpq : degree p < degree q
then begin
  rw [(div_by_monic_eq_zero_iff hq hq0).2 hpq, degree_eq_nat_degree hp0],
  exact with_bot.bot_lt_some _
end
else begin
  rw [← degree_add_div_by_monic hq (not_lt.1 hpq), degree_eq_nat_degree hq0,
        degree_eq_nat_degree (mt (div_by_monic_eq_zero_iff hq hq0).1 hpq)],
  exact with_bot.coe_lt_coe.2 (nat.lt_add_of_pos_left
    (with_bot.coe_lt_coe.1 $ (degree_eq_nat_degree hq0) ▸ h0q))
end

lemma div_mod_by_monic_unique {f g} (q r : polynomial R) (hg : monic g)
  (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ g = r :=
if hg0 : g = 0 then by split; exact (subsingleton_of_monic_zero
  (hg0 ▸ hg : monic (0 : polynomial R))).1 _ _
else
  have h₁ : r - f %ₘ g = -g * (q - f /ₘ g),
    from eq_of_sub_eq_zero
      (by rw [← sub_eq_zero_of_eq (h.1.trans (mod_by_monic_add_div f hg).symm)];
        simp [mul_add, mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]),
  have h₂ : degree (r - f %ₘ g) = degree (g * (q - f /ₘ g)),
    by simp [h₁],
  have h₄ : degree (r - f %ₘ g) < degree g,
    from calc degree (r - f %ₘ g) ≤ max (degree r) (degree (-(f %ₘ g))) :
      degree_add_le _ _
    ... < degree g : max_lt_iff.2 ⟨h.2, by rw degree_neg; exact degree_mod_by_monic_lt _ hg hg0⟩,
  have h₅ : q - (f /ₘ g) = 0,
    from by_contradiction
      (λ hqf, not_le_of_gt h₄ $
        calc degree g ≤ degree g + degree (q - f /ₘ g) :
          by erw [degree_eq_nat_degree hg0, degree_eq_nat_degree hqf,
              with_bot.coe_le_coe];
            exact nat.le_add_right _ _
        ... = degree (r - f %ₘ g) :
          by rw [h₂, degree_mul_eq']; simpa [monic.def.1 hg]),
  ⟨eq.symm $ eq_of_sub_eq_zero h₅,
    eq.symm $ eq_of_sub_eq_zero $ by simpa [h₅] using h₁⟩

lemma map_mod_div_by_monic [comm_ring S] (f : R →+* S) (hq : monic q) :
  (p /ₘ q).map f = p.map f /ₘ q.map f ∧ (p %ₘ q).map f = p.map f %ₘ q.map f :=
if h01 : (0 : S) = 1 then by haveI := subsingleton_of_zero_eq_one S h01;
  exact ⟨subsingleton.elim _ _, subsingleton.elim _ _⟩
else
have h01R : (0 : R) ≠ 1, from mt (congr_arg f)
  (by rwa [is_semiring_hom.map_one f, is_semiring_hom.map_zero f]),
have map f p /ₘ map f q = map f (p /ₘ q) ∧ map f p %ₘ map f q = map f (p %ₘ q),
  from (div_mod_by_monic_unique ((p /ₘ q).map f) _ (monic_map f hq)
    ⟨eq.symm $ by rw [← map_mul, ← map_add, mod_by_monic_add_div _ hq],
    calc _ ≤ degree (p %ₘ q) : degree_map_le _
    ... < degree q : degree_mod_by_monic_lt _ hq
      $ (ne_zero_of_monic_of_zero_ne_one hq h01R)
    ... = _ : eq.symm $ degree_map_eq_of_leading_coeff_ne_zero _
      (by rw [monic.def.1 hq, is_semiring_hom.map_one f]; exact ne.symm h01)⟩),
⟨this.1.symm, this.2.symm⟩

lemma map_div_by_monic [comm_ring S] (f : R →+* S) (hq : monic q) :
  (p /ₘ q).map f = p.map f /ₘ q.map f :=
(map_mod_div_by_monic f hq).1

lemma map_mod_by_monic [comm_ring S] (f : R →+* S) (hq : monic q) :
  (p %ₘ q).map f = p.map f %ₘ q.map f :=
(map_mod_div_by_monic f hq).2

lemma dvd_iff_mod_by_monic_eq_zero (hq : monic q) : p %ₘ q = 0 ↔ q ∣ p :=
⟨λ h, by rw [← mod_by_monic_add_div p hq, h, zero_add];
  exact dvd_mul_right _ _,
λ h, if hq0 : q = 0 then by rw hq0 at hq;
  exact (subsingleton_of_monic_zero hq).1 _ _
  else
  let ⟨r, hr⟩ := exists_eq_mul_right_of_dvd h in
  by_contradiction (λ hpq0,
  have hmod : p %ₘ q = q * (r - p /ₘ q) :=
    by rw [mod_by_monic_eq_sub_mul_div _ hq, mul_sub, ← hr],
  have degree (q * (r - p /ₘ q)) < degree q :=
    hmod ▸ degree_mod_by_monic_lt _ hq hq0,
  have hrpq0 : leading_coeff (r - p /ₘ q) ≠ 0 :=
    λ h, hpq0 $ leading_coeff_eq_zero.1
      (by rw [hmod, leading_coeff_eq_zero.1 h, mul_zero, leading_coeff_zero]),
  have hlc : leading_coeff q * leading_coeff (r - p /ₘ q) ≠ 0 :=
    by rwa [monic.def.1 hq, one_mul],
  by rw [degree_mul_eq' hlc, degree_eq_nat_degree hq0,
      degree_eq_nat_degree (mt leading_coeff_eq_zero.2 hrpq0)] at this;
    exact not_lt_of_ge (nat.le_add_right _ _) (with_bot.some_lt_some.1 this))⟩

@[simp] lemma mod_by_monic_one (p : polynomial R) : p %ₘ 1 = 0 :=
(dvd_iff_mod_by_monic_eq_zero monic_one).2 (one_dvd _)

@[simp] lemma div_by_monic_one (p : polynomial R) : p /ₘ 1 = p :=
by conv_rhs { rw [← mod_by_monic_add_div p monic_one] }; simp

lemma degree_pos_of_root (hp : p ≠ 0) (h : is_root p a) : 0 < degree p :=
lt_of_not_ge $ λ hlt, begin
  have := eq_C_of_degree_le_zero hlt,
  rw [is_root, this, eval_C] at h,
  exact hp (finsupp.ext (λ n, show coeff p n = 0, from
    nat.cases_on n h (λ _, coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hlt
      (with_bot.coe_lt_coe.2 (nat.succ_pos _)))))),
end

theorem monic_X_sub_C (x : R) : monic (X - C x) :=
by simpa only [C_neg] using monic_X_add_C (-x)

theorem monic_X_pow_sub {n : ℕ} (H : degree p ≤ n) : monic (X ^ (n+1) - p) :=
monic_X_pow_add ((degree_neg p).symm ▸ H)

theorem degree_mod_by_monic_le (p : polynomial R) {q : polynomial R}
  (hq : monic q) : degree (p %ₘ q) ≤ degree q :=
decidable.by_cases
  (assume H : q = 0, by rw [monic, H, leading_coeff_zero] at hq;
    have : (0:polynomial R) = 1 := (by rw [← C_0, ← C_1, hq]);
    rw [eq_zero_of_zero_eq_one _ this (p %ₘ q), eq_zero_of_zero_eq_one _ this q]; exact le_refl _)
  (assume H : q ≠ 0, le_of_lt $ degree_mod_by_monic_lt _ hq H)

lemma root_X_sub_C : is_root (X - C a) b ↔ a = b :=
by rw [is_root.def, eval_sub, eval_X, eval_C, sub_eq_zero_iff_eq, eq_comm]

end comm_ring

section nonzero_comm_ring
variables [comm_ring R] [nonzero R] {p q : polynomial R}

@[simp] lemma degree_X_sub_C (a : R) : degree (X - C a) = 1 :=
begin
  rw [sub_eq_add_neg, add_comm, ← @degree_X R],
  by_cases ha : a = 0,
  { simp only [ha, C_0, neg_zero, zero_add] },
  exact degree_add_eq_of_degree_lt (by rw [degree_X, degree_neg, degree_C ha]; exact dec_trivial)
end

lemma degree_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) :
  degree ((X : polynomial R) ^ n - C a) = n :=
have degree (-C a) < degree ((X : polynomial R) ^ n),
  from calc degree (-C a) ≤ 0 : by rw degree_neg; exact degree_C_le
  ... < degree ((X : polynomial R) ^ n) : by rwa [degree_X_pow];
    exact with_bot.coe_lt_coe.2 hn,
by rw [sub_eq_add_neg, add_comm, degree_add_eq_of_degree_lt this, degree_X_pow]

lemma X_pow_sub_C_ne_zero {n : ℕ} (hn : 0 < n) (a : R) :
  (X : polynomial R) ^ n - C a ≠ 0 :=
mt degree_eq_bot.2 (show degree ((X : polynomial R) ^ n - C a) ≠ ⊥,
  by rw degree_X_pow_sub_C hn a; exact dec_trivial)

end nonzero_comm_ring

section comm_ring

variables [comm_ring R] {p q : polynomial R}

@[simp] lemma mod_by_monic_X_sub_C_eq_C_eval (p : polynomial R) (a : R) :
  p %ₘ (X - C a) = C (p.eval a) :=
if h0 : (0 : R) = 1 then by letI := subsingleton_of_zero_eq_one R h0; exact subsingleton.elim _ _
else
by letI : nonzero R := nonzero.of_ne h0; exact
have h : (p %ₘ (X - C a)).eval a = p.eval a :=
  by rw [mod_by_monic_eq_sub_mul_div _ (monic_X_sub_C a), eval_sub, eval_mul,
    eval_sub, eval_X, eval_C, sub_self, zero_mul, sub_zero],
have degree (p %ₘ (X - C a)) < 1 :=
  degree_X_sub_C a ▸ degree_mod_by_monic_lt p (monic_X_sub_C a) ((degree_X_sub_C a).symm ▸
    ne_zero_of_monic (monic_X_sub_C _)),
have degree (p %ₘ (X - C a)) ≤ 0 :=
  begin
    cases (degree (p %ₘ (X - C a))),
    { exact bot_le },
    { exact with_bot.some_le_some.2 (nat.le_of_lt_succ (with_bot.some_lt_some.1 this)) }
  end,
begin
  rw [eq_C_of_degree_le_zero this, eval_C] at h,
  rw [eq_C_of_degree_le_zero this, h]
end

lemma mul_div_by_monic_eq_iff_is_root : (X - C a) * (p /ₘ (X - C a)) = p ↔ is_root p a :=
⟨λ h, by rw [← h, is_root.def, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul],
λ h : p.eval a = 0,
  by conv {to_rhs, rw ← mod_by_monic_add_div p (monic_X_sub_C a)};
    rw [mod_by_monic_X_sub_C_eq_C_eval, h, C_0, zero_add]⟩

lemma dvd_iff_is_root : (X - C a) ∣ p ↔ is_root p a :=
⟨λ h, by rwa [← dvd_iff_mod_by_monic_eq_zero (monic_X_sub_C _),
    mod_by_monic_X_sub_C_eq_C_eval, ← C_0, C_inj] at h,
  λ h, ⟨(p /ₘ (X - C a)), by rw mul_div_by_monic_eq_iff_is_root.2 h⟩⟩

lemma mod_by_monic_X (p : polynomial R) : p %ₘ X = C (p.eval 0) :=
by rw [← mod_by_monic_X_sub_C_eq_C_eval, C_0, sub_zero]

section multiplicity

def decidable_dvd_monic (p : polynomial R) (hq : monic q) : decidable (q ∣ p) :=
decidable_of_iff (p %ₘ q = 0) (dvd_iff_mod_by_monic_eq_zero hq)

open_locale classical

lemma multiplicity_X_sub_C_finite (a : R) (h0 : p ≠ 0) :
  multiplicity.finite (X - C a) p :=
multiplicity_finite_of_degree_pos_of_monic
  (have (0 : R) ≠ 1, from (λ h, by haveI := subsingleton_of_zero_eq_one _ h;
      exact h0 (subsingleton.elim _ _)),
    by haveI : nonzero R := ⟨this⟩; rw degree_X_sub_C; exact dec_trivial)
    (monic_X_sub_C _) h0

def root_multiplicity (a : R) (p : polynomial R) : ℕ :=
if h0 : p = 0 then 0
else let I : decidable_pred (λ n : ℕ, ¬(X - C a) ^ (n + 1) ∣ p) :=
  λ n, @not.decidable _ (decidable_dvd_monic p (monic_pow (monic_X_sub_C a) (n + 1))) in
by exactI nat.find (multiplicity_X_sub_C_finite a h0)

lemma root_multiplicity_eq_multiplicity (p : polynomial R) (a : R) :
  root_multiplicity a p = if h0 : p = 0 then 0 else
  (multiplicity (X - C a) p).get (multiplicity_X_sub_C_finite a h0) :=
by simp [multiplicity, root_multiplicity, roption.dom];
  congr; funext; congr

lemma pow_root_multiplicity_dvd (p : polynomial R) (a : R) :
  (X - C a) ^ root_multiplicity a p ∣ p :=
if h : p = 0 then by simp [h]
else by rw [root_multiplicity_eq_multiplicity, dif_neg h];
  exact multiplicity.pow_multiplicity_dvd _

lemma div_by_monic_mul_pow_root_multiplicity_eq
  (p : polynomial R) (a : R) :
  p /ₘ ((X - C a) ^ root_multiplicity a p) *
  (X - C a) ^ root_multiplicity a p = p :=
have monic ((X - C a) ^ root_multiplicity a p),
  from monic_pow (monic_X_sub_C _) _,
by conv_rhs { rw [← mod_by_monic_add_div p this,
    (dvd_iff_mod_by_monic_eq_zero this).2 (pow_root_multiplicity_dvd _ _)] };
  simp [mul_comm]

lemma eval_div_by_monic_pow_root_multiplicity_ne_zero
  {p : polynomial R} (a : R) (hp : p ≠ 0) :
  (p /ₘ ((X - C a) ^ root_multiplicity a p)).eval a ≠ 0 :=
begin
  haveI : nonzero R := nonzero.of_polynomial_ne hp,
  rw [ne.def, ← is_root.def, ← dvd_iff_is_root],
  rintros ⟨q, hq⟩,
  have := div_by_monic_mul_pow_root_multiplicity_eq p a,
  rw [mul_comm, hq, ← mul_assoc, ← pow_succ',
    root_multiplicity_eq_multiplicity, dif_neg hp] at this,
  exact multiplicity.is_greatest'
    (multiplicity_finite_of_degree_pos_of_monic
    (show (0 : with_bot ℕ) < degree (X - C a),
      by rw degree_X_sub_C; exact dec_trivial) (monic_X_sub_C _) hp)
    (nat.lt_succ_self _) (dvd_of_mul_right_eq _ this)
end

end multiplicity

end comm_ring

section integral_domain
variables [integral_domain R] {p q : polynomial R}

@[simp] lemma degree_mul_eq : degree (p * q) = degree p + degree q :=
if hp0 : p = 0 then by simp only [hp0, degree_zero, zero_mul, with_bot.bot_add]
else if hq0 : q = 0 then  by simp only [hq0, degree_zero, mul_zero, with_bot.add_bot]
else degree_mul_eq' $ mul_ne_zero (mt leading_coeff_eq_zero.1 hp0)
    (mt leading_coeff_eq_zero.1 hq0)

@[simp] lemma degree_pow_eq (p : polynomial R) (n : ℕ) :
  degree (p ^ n) = n •ℕ (degree p) :=
by induction n; [simp only [pow_zero, degree_one, zero_nsmul],
simp only [*, pow_succ, succ_nsmul, degree_mul_eq]]

@[simp] lemma leading_coeff_mul (p q : polynomial R) : leading_coeff (p * q) =
  leading_coeff p * leading_coeff q :=
begin
  by_cases hp : p = 0,
  { simp only [hp, zero_mul, leading_coeff_zero] },
  { by_cases hq : q = 0,
    { simp only [hq, mul_zero, leading_coeff_zero] },
    { rw [leading_coeff_mul'],
      exact mul_ne_zero (mt leading_coeff_eq_zero.1 hp) (mt leading_coeff_eq_zero.1 hq) } }
end

@[simp] lemma leading_coeff_pow (p : polynomial R) (n : ℕ) :
  leading_coeff (p ^ n) = leading_coeff p ^ n :=
by induction n; [simp only [pow_zero, leading_coeff_one],
simp only [*, pow_succ, leading_coeff_mul]]

instance : integral_domain (polynomial R) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b h, begin
    have : leading_coeff 0 = leading_coeff a * leading_coeff b := h ▸ leading_coeff_mul a b,
    rw [leading_coeff_zero, eq_comm] at this,
    erw [← leading_coeff_eq_zero, ← leading_coeff_eq_zero],
    exact eq_zero_or_eq_zero_of_mul_eq_zero this
  end,
  ..polynomial.nonzero,
  ..polynomial.comm_ring }

lemma nat_degree_mul_eq (hp : p ≠ 0) (hq : q ≠ 0) : nat_degree (p * q) =
  nat_degree p + nat_degree q :=
by rw [← with_bot.coe_eq_coe, ← degree_eq_nat_degree (mul_ne_zero hp hq),
    with_bot.coe_add, ← degree_eq_nat_degree hp,
    ← degree_eq_nat_degree hq, degree_mul_eq]

@[simp] lemma nat_degree_pow_eq (p : polynomial R) (n : ℕ) :
  nat_degree (p ^ n) = n * nat_degree p :=
if hp0 : p = 0
then if hn0 : n = 0 then by simp [hp0, hn0]
  else by rw [hp0, zero_pow (nat.pos_of_ne_zero hn0)]; simp
else nat_degree_pow_eq'
  (by rw [← leading_coeff_pow, ne.def, leading_coeff_eq_zero]; exact pow_ne_zero _ hp0)

lemma root_or_root_of_root_mul (h : is_root (p * q) a) : is_root p a ∨ is_root q a :=
by rw [is_root, eval_mul] at h;
  exact eq_zero_or_eq_zero_of_mul_eq_zero h

lemma degree_le_mul_left (p : polynomial R) (hq : q ≠ 0) : degree p ≤ degree (p * q) :=
if hp : p = 0 then by simp only [hp, zero_mul, le_refl]
else by rw [degree_mul_eq, degree_eq_nat_degree hp,
    degree_eq_nat_degree hq];
  exact with_bot.coe_le_coe.2 (nat.le_add_right _ _)

lemma exists_finset_roots : ∀ {p : polynomial R} (hp : p ≠ 0),
  ∃ s : finset R, (s.card : with_bot ℕ) ≤ degree p ∧ ∀ x, x ∈ s ↔ is_root p x
| p := λ hp, by haveI := classical.prop_decidable (∃ x, is_root p x); exact
if h : ∃ x, is_root p x
then
  let ⟨x, hx⟩ := h in
  have hpd : 0 < degree p := degree_pos_of_root hp hx,
  have hd0 : p /ₘ (X - C x) ≠ 0 :=
    λ h, by rw [← mul_div_by_monic_eq_iff_is_root.2 hx, h, mul_zero] at hp; exact hp rfl,
  have wf : degree (p /ₘ _) < degree p :=
    degree_div_by_monic_lt _ (monic_X_sub_C x) hp
    ((degree_X_sub_C x).symm ▸ dec_trivial),
  let ⟨t, htd, htr⟩ := @exists_finset_roots (p /ₘ (X - C x)) hd0 in
  have hdeg : degree (X - C x) ≤ degree p := begin
    rw [degree_X_sub_C, degree_eq_nat_degree hp],
    rw degree_eq_nat_degree hp at hpd,
    exact with_bot.coe_le_coe.2 (with_bot.coe_lt_coe.1 hpd)
  end,
  have hdiv0 : p /ₘ (X - C x) ≠ 0 := mt (div_by_monic_eq_zero_iff (monic_X_sub_C x)
    (ne_zero_of_monic (monic_X_sub_C x))).1 $ not_lt.2 hdeg,
  ⟨insert x t, calc (card (insert x t) : with_bot ℕ) ≤ card t + 1 :
    with_bot.coe_le_coe.2 $ finset.card_insert_le _ _
    ... ≤ degree p :
      by rw [← degree_add_div_by_monic (monic_X_sub_C x) hdeg,
          degree_X_sub_C, add_comm];
        exact add_le_add' (le_refl (1 : with_bot ℕ)) htd,
  begin
    assume y,
    rw [mem_insert, htr, eq_comm, ← root_X_sub_C],
    conv {to_rhs, rw ← mul_div_by_monic_eq_iff_is_root.2 hx},
    exact ⟨λ h, or.cases_on h (root_mul_right_of_is_root _) (root_mul_left_of_is_root _),
      root_or_root_of_root_mul⟩
  end⟩
else
  ⟨∅, (degree_eq_nat_degree hp).symm ▸ with_bot.coe_le_coe.2 (nat.zero_le _),
    by simpa only [not_mem_empty, false_iff, not_exists] using h⟩
using_well_founded {dec_tac := tactic.assumption}

/-- `roots p` noncomputably gives a finset containing all the roots of `p` -/
noncomputable def roots (p : polynomial R) : finset R :=
if h : p = 0 then ∅ else classical.some (exists_finset_roots h)

lemma card_roots (hp0 : p ≠ 0) : ((roots p).card : with_bot ℕ) ≤ degree p :=
begin
  unfold roots,
  rw dif_neg hp0,
  exact (classical.some_spec (exists_finset_roots hp0)).1
end

lemma card_roots' {p : polynomial R} (hp0 : p ≠ 0) : p.roots.card ≤ nat_degree p :=
with_bot.coe_le_coe.1 (le_trans (card_roots hp0) (le_of_eq $ degree_eq_nat_degree hp0))

lemma card_roots_sub_C {p : polynomial R} {a : R} (hp0 : 0 < degree p) :
  ((p - C a).roots.card : with_bot ℕ) ≤ degree p :=
calc ((p - C a).roots.card : with_bot ℕ) ≤ degree (p - C a) :
  card_roots $ mt sub_eq_zero.1 $ λ h, not_le_of_gt hp0 $ h.symm ▸ degree_C_le
... = degree p : by rw [sub_eq_add_neg, ← C_neg]; exact degree_add_C hp0

lemma card_roots_sub_C' {p : polynomial R} {a : R} (hp0 : 0 < degree p) :
  (p - C a).roots.card ≤ nat_degree p :=
with_bot.coe_le_coe.1 (le_trans (card_roots_sub_C hp0) (le_of_eq $ degree_eq_nat_degree
  (λ h, by simp [*, lt_irrefl] at *)))

@[simp] lemma mem_roots (hp : p ≠ 0) : a ∈ p.roots ↔ is_root p a :=
by unfold roots; rw dif_neg hp; exact (classical.some_spec (exists_finset_roots hp)).2 _

@[simp] lemma mem_roots_sub_C {p : polynomial R} {a x : R} (hp0 : 0 < degree p) :
  x ∈ (p - C a).roots ↔ p.eval x = a :=
(mem_roots (show p - C a ≠ 0, from mt sub_eq_zero.1 $ λ h,
    not_le_of_gt hp0 $ h.symm ▸ degree_C_le)).trans
  (by rw [is_root.def, eval_sub, eval_C, sub_eq_zero])

lemma card_roots_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) :
  (roots ((X : polynomial R) ^ n - C a)).card ≤ n :=
with_bot.coe_le_coe.1 $
calc ((roots ((X : polynomial R) ^ n - C a)).card : with_bot ℕ)
      ≤ degree ((X : polynomial R) ^ n - C a) : card_roots (X_pow_sub_C_ne_zero hn a)
  ... = n : degree_X_pow_sub_C hn a

/-- `nth_roots n a` noncomputably returns the solutions to `x ^ n = a`-/
def nth_roots {R : Type*} [integral_domain R] (n : ℕ) (a : R) : finset R :=
roots ((X : polynomial R) ^ n - C a)

@[simp] lemma mem_nth_roots {R : Type*} [integral_domain R] {n : ℕ} (hn : 0 < n) {a x : R} :
  x ∈ nth_roots n a ↔ x ^ n = a :=
by rw [nth_roots, mem_roots (X_pow_sub_C_ne_zero hn a),
  is_root.def, eval_sub, eval_C, eval_pow, eval_X, sub_eq_zero_iff_eq]

lemma card_nth_roots {R : Type*} [integral_domain R] (n : ℕ) (a : R) :
  (nth_roots n a).card ≤ n :=
if hn : n = 0
then if h : (X : polynomial R) ^ n - C a = 0
  then by simp only [nat.zero_le, nth_roots, roots, h, dif_pos rfl, card_empty]
  else with_bot.coe_le_coe.1 (le_trans (card_roots h)
   (by rw [hn, pow_zero, ← C_1, ← @is_ring_hom.map_sub _ _ _ _ (@C R _)];
      exact degree_C_le))
else by rw [← with_bot.coe_le_coe, ← degree_X_pow_sub_C (nat.pos_of_ne_zero hn) a];
  exact card_roots (X_pow_sub_C_ne_zero (nat.pos_of_ne_zero hn) a)

lemma coeff_comp_degree_mul_degree (hqd0 : nat_degree q ≠ 0) :
  coeff (p.comp q) (nat_degree p * nat_degree q) =
  leading_coeff p * leading_coeff q ^ nat_degree p :=
if hp0 : p = 0 then by simp [hp0] else
calc coeff (p.comp q) (nat_degree p * nat_degree q)
  = p.sum (λ n a, coeff (C a * q ^ n) (nat_degree p * nat_degree q)) :
    by rw [comp, eval₂, coeff_sum]
... = coeff (C (leading_coeff p) * q ^ nat_degree p) (nat_degree p * nat_degree q) :
  finset.sum_eq_single _
  begin
    assume b hbs hbp,
    have hq0 : q ≠ 0, from λ hq0, hqd0 (by rw [hq0, nat_degree_zero]),
    have : coeff p b ≠ 0, rwa [← apply_eq_coeff, ← finsupp.mem_support_iff],
    dsimp [apply_eq_coeff],
    refine coeff_eq_zero_of_degree_lt _,
    rw [degree_mul_eq, degree_C this, degree_pow_eq, zero_add, degree_eq_nat_degree hq0,
      ← with_bot.coe_nsmul, nsmul_eq_mul, with_bot.coe_lt_coe, nat.cast_id],
    exact (mul_lt_mul_right (nat.pos_of_ne_zero hqd0)).2
      (lt_of_le_of_ne (with_bot.coe_le_coe.1 (by rw ← degree_eq_nat_degree hp0; exact le_sup hbs))
        hbp)
  end
  (by rw [finsupp.mem_support_iff, apply_eq_coeff, ← leading_coeff, ne.def, leading_coeff_eq_zero,
      classical.not_not]; simp {contextual := tt})
... = _ :
  have coeff (q ^ nat_degree p) (nat_degree p * nat_degree q) = leading_coeff (q ^ nat_degree p),
    by rw [leading_coeff, nat_degree_pow_eq],
  by rw [coeff_C_mul, this, leading_coeff_pow]

lemma nat_degree_comp : nat_degree (p.comp q) = nat_degree p * nat_degree q :=
le_antisymm nat_degree_comp_le
  (if hp0 : p = 0 then by rw [hp0, zero_comp, nat_degree_zero, zero_mul]
  else if hqd0 : nat_degree q = 0
  then have degree q ≤ 0, by rw [← with_bot.coe_zero, ← hqd0]; exact degree_le_nat_degree,
    by rw [eq_C_of_degree_le_zero this]; simp
  else le_nat_degree_of_ne_zero $
    have hq0 : q ≠ 0, from λ hq0, hqd0 $ by rw [hq0, nat_degree_zero],
    calc coeff (p.comp q) (nat_degree p * nat_degree q)
        = leading_coeff p * leading_coeff q ^ nat_degree p :
      coeff_comp_degree_mul_degree hqd0
    ... ≠ 0 : mul_ne_zero (mt leading_coeff_eq_zero.1 hp0)
      (pow_ne_zero _ (mt leading_coeff_eq_zero.1 hq0)))

lemma leading_coeff_comp (hq : nat_degree q ≠ 0) : leading_coeff (p.comp q) =
  leading_coeff p * leading_coeff q ^ nat_degree p :=
by rw [← coeff_comp_degree_mul_degree hq, ← nat_degree_comp]; refl

lemma degree_eq_zero_of_is_unit (h : is_unit p) : degree p = 0 :=
let ⟨q, hq⟩ := is_unit_iff_dvd_one.1 h in
have hp0 : p ≠ 0, from λ hp0, by simpa [hp0] using hq,
have hq0 : q ≠ 0, from λ hp0, by simpa [hp0] using hq,
have nat_degree (1 : polynomial R) = nat_degree (p * q),
  from congr_arg _ hq,
by rw [nat_degree_one, nat_degree_mul_eq hp0 hq0, eq_comm,
    _root_.add_eq_zero_iff, ← with_bot.coe_eq_coe,
    ← degree_eq_nat_degree hp0] at this;
  exact this.1

@[simp] lemma degree_coe_units (u : units (polynomial R)) :
  degree (u : polynomial R) = 0 :=
degree_eq_zero_of_is_unit ⟨u, rfl⟩

@[simp] lemma nat_degree_coe_units (u : units (polynomial R)) :
  nat_degree (u : polynomial R) = 0 :=
nat_degree_eq_of_degree_eq_some (degree_coe_units u)

lemma coeff_coe_units_zero_ne_zero (u : units (polynomial R)) :
  coeff (u : polynomial R) 0 ≠ 0 :=
begin
  conv in (0) {rw [← nat_degree_coe_units u]},
  rw [← leading_coeff, ne.def, leading_coeff_eq_zero],
  exact units.coe_ne_zero _
end

lemma degree_eq_degree_of_associated (h : associated p q) : degree p = degree q :=
let ⟨u, hu⟩ := h in by simp [hu.symm]

lemma degree_eq_one_of_irreducible_of_root (hi : irreducible p) {x : R} (hx : is_root p x) :
  degree p = 1 :=
let ⟨g, hg⟩ := dvd_iff_is_root.2 hx in
have is_unit (X - C x) ∨ is_unit g, from hi.2 _ _ hg,
this.elim
  (λ h, have h₁ : degree (X - C x) = 1, from degree_X_sub_C x,
    have h₂ : degree (X - C x) = 0, from degree_eq_zero_of_is_unit h,
    by rw h₁ at h₂; exact absurd h₂ dec_trivial)
  (λ hgu, by rw [hg, degree_mul_eq, degree_X_sub_C, degree_eq_zero_of_is_unit hgu, add_zero])

lemma prime_of_degree_eq_one_of_monic (hp1 : degree p = 1)
  (hm : monic p) : prime p :=
have p = X - C (- p.coeff 0),
  by simpa [hm.leading_coeff] using eq_X_add_C_of_degree_eq_one hp1,
⟨mt degree_eq_bot.2 $ hp1.symm ▸ dec_trivial,
  mt degree_eq_zero_of_is_unit (by simp [hp1]; exact dec_trivial),
    λ _ _, begin
      rw [this, dvd_iff_is_root, dvd_iff_is_root, dvd_iff_is_root,
        is_root, is_root, is_root, eval_mul, mul_eq_zero],
      exact id
    end⟩

lemma irreducible_of_degree_eq_one_of_monic (hp1 : degree p = 1)
  (hm : monic p) : irreducible p :=
irreducible_of_prime (prime_of_degree_eq_one_of_monic hp1 hm)

end integral_domain

section field
variables [field R] {p q : polynomial R}
instance : vector_space R (polynomial R) := finsupp.vector_space _ _

lemma is_unit_iff_degree_eq_zero : is_unit p ↔ degree p = 0 :=
⟨degree_eq_zero_of_is_unit,
  λ h, have degree p ≤ 0, by simp [*, le_refl],
    have hc : coeff p 0 ≠ 0, from λ hc,
        by rw [eq_C_of_degree_le_zero this, hc] at h;
        simpa using h,
    is_unit_iff_dvd_one.2 ⟨C (coeff p 0)⁻¹, begin
      conv in p { rw eq_C_of_degree_le_zero this },
      rw [← C_mul, _root_.mul_inv_cancel hc, C_1]
    end⟩⟩

lemma degree_pos_of_ne_zero_of_nonunit (hp0 : p ≠ 0) (hp : ¬is_unit p) :
  0 < degree p :=
lt_of_not_ge (λ h, by rw [eq_C_of_degree_le_zero h] at hp0 hp;
  exact (hp $ is_unit.map' C $
    is_unit.mk0 (coeff p 0) (mt C_inj.2 (by simpa using hp0))))

lemma monic_mul_leading_coeff_inv (h : p ≠ 0) :
  monic (p * C (leading_coeff p)⁻¹) :=
by rw [monic, leading_coeff_mul, leading_coeff_C,
  mul_inv_cancel (show leading_coeff p ≠ 0, from mt leading_coeff_eq_zero.1 h)]

lemma degree_mul_leading_coeff_inv (p : polynomial R) (h : q ≠ 0) :
  degree (p * C (leading_coeff q)⁻¹) = degree p :=
have h₁ : (leading_coeff q)⁻¹ ≠ 0 :=
  inv_ne_zero (mt leading_coeff_eq_zero.1 h),
by rw [degree_mul_eq, degree_C h₁, add_zero]

def div (p q : polynomial R) :=
C (leading_coeff q)⁻¹ * (p /ₘ (q * C (leading_coeff q)⁻¹))

def mod (p q : polynomial R) :=
p %ₘ (q * C (leading_coeff q)⁻¹)

private lemma quotient_mul_add_remainder_eq_aux (p q : polynomial R) :
  q * div p q + mod p q = p :=
if h : q = 0 then by simp only [h, zero_mul, mod, mod_by_monic_zero, zero_add]
else begin
  conv {to_rhs, rw ← mod_by_monic_add_div p (monic_mul_leading_coeff_inv h)},
  rw [div, mod, add_comm, mul_assoc]
end

private lemma remainder_lt_aux (p : polynomial R) (hq : q ≠ 0) :
  degree (mod p q) < degree q :=
by rw ← degree_mul_leading_coeff_inv q hq; exact
  degree_mod_by_monic_lt p (monic_mul_leading_coeff_inv hq)
    (mul_ne_zero hq (mt leading_coeff_eq_zero.2 (by rw leading_coeff_C;
      exact inv_ne_zero (mt leading_coeff_eq_zero.1 hq))))

instance : has_div (polynomial R) := ⟨div⟩

instance : has_mod (polynomial R) := ⟨mod⟩

lemma div_def : p / q = C (leading_coeff q)⁻¹ * (p /ₘ (q * C (leading_coeff q)⁻¹)) := rfl

lemma mod_def : p % q = p %ₘ (q * C (leading_coeff q)⁻¹) := rfl

lemma mod_by_monic_eq_mod (p : polynomial R) (hq : monic q) : p %ₘ q = p % q :=
show p %ₘ q = p %ₘ (q * C (leading_coeff q)⁻¹), by simp only [monic.def.1 hq, inv_one, mul_one, C_1]

lemma div_by_monic_eq_div (p : polynomial R) (hq : monic q) : p /ₘ q = p / q :=
show p /ₘ q = C (leading_coeff q)⁻¹ * (p /ₘ (q * C (leading_coeff q)⁻¹)),
by simp only [monic.def.1 hq, inv_one, C_1, one_mul, mul_one]

lemma mod_X_sub_C_eq_C_eval (p : polynomial R) (a : R) : p % (X - C a) = C (p.eval a) :=
mod_by_monic_eq_mod p (monic_X_sub_C a) ▸ mod_by_monic_X_sub_C_eq_C_eval _ _

lemma mul_div_eq_iff_is_root : (X - C a) * (p / (X - C a)) = p ↔ is_root p a :=
div_by_monic_eq_div p (monic_X_sub_C a) ▸ mul_div_by_monic_eq_iff_is_root

instance : euclidean_domain (polynomial R) :=
{ quotient := (/),
  quotient_zero := by simp [div_def],
  remainder := (%),
  r := _,
  r_well_founded := degree_lt_wf,
  quotient_mul_add_remainder_eq := quotient_mul_add_remainder_eq_aux,
  remainder_lt := λ p q hq, remainder_lt_aux _ hq,
  mul_left_not_lt := λ p q hq, not_lt_of_ge (degree_le_mul_left _ hq),
  .. polynomial.comm_ring,
  .. polynomial.nonzero }

lemma mod_eq_self_iff (hq0 : q ≠ 0) : p % q = p ↔ degree p < degree q :=
⟨λ h, h ▸ euclidean_domain.mod_lt _ hq0,
λ h, have ¬degree (q * C (leading_coeff q)⁻¹) ≤ degree p :=
  not_le_of_gt $ by rwa degree_mul_leading_coeff_inv q hq0,
begin
  rw [mod_def, mod_by_monic, dif_pos (monic_mul_leading_coeff_inv hq0)],
  unfold div_mod_by_monic_aux,
  simp only [this, false_and, if_false]
end⟩

lemma div_eq_zero_iff (hq0 : q ≠ 0) : p / q = 0 ↔ degree p < degree q :=
⟨λ h, by have := euclidean_domain.div_add_mod p q;
  rwa [h, mul_zero, zero_add, mod_eq_self_iff hq0] at this,
λ h, have hlt : degree p < degree (q * C (leading_coeff q)⁻¹),
    by rwa degree_mul_leading_coeff_inv q hq0,
  have hm : monic (q * C (leading_coeff q)⁻¹) := monic_mul_leading_coeff_inv hq0,
  by rw [div_def, (div_by_monic_eq_zero_iff hm (ne_zero_of_monic hm)).2 hlt, mul_zero]⟩

lemma degree_add_div (hq0 : q ≠ 0) (hpq : degree q ≤ degree p) :
  degree q + degree (p / q) = degree p :=
have degree (p % q) < degree (q * (p / q)) :=
  calc degree (p % q) < degree q : euclidean_domain.mod_lt _ hq0
  ... ≤ _ : degree_le_mul_left _ (mt (div_eq_zero_iff hq0).1 (not_lt_of_ge hpq)),
by conv {to_rhs, rw [← euclidean_domain.div_add_mod p q, add_comm,
    degree_add_eq_of_degree_lt this, degree_mul_eq]}

lemma degree_div_le (p q : polynomial R) : degree (p / q) ≤ degree p :=
if hq : q = 0 then by simp [hq]
else by rw [div_def, mul_comm, degree_mul_leading_coeff_inv _ hq];
  exact degree_div_by_monic_le _ _

lemma degree_div_lt (hp : p ≠ 0) (hq : 0 < degree q) : degree (p / q) < degree p :=
have hq0 : q ≠ 0, from λ hq0, by simpa [hq0] using hq,
by rw [div_def, mul_comm, degree_mul_leading_coeff_inv _ hq0];
  exact degree_div_by_monic_lt _ (monic_mul_leading_coeff_inv hq0) hp
    (by rw degree_mul_leading_coeff_inv _ hq0; exact hq)

@[simp] lemma degree_map [field k] (p : polynomial R) (f : R →+* k) :
  degree (p.map f) = degree p :=
p.degree_map_eq_of_injective (is_ring_hom.injective f)

@[simp] lemma nat_degree_map [field k] (f : R →+* k) :
  nat_degree (p.map f) = nat_degree p :=
nat_degree_eq_of_degree_eq (degree_map _ f)

@[simp] lemma leading_coeff_map [field k] (f : R →+* k) :
  leading_coeff (p.map f) = f (leading_coeff p) :=
by simp [leading_coeff, coeff_map f]

lemma map_div [field k] (f : R →+* k) :
  (p / q).map f = p.map f / q.map f :=
if hq0 : q = 0 then by simp [hq0]
else
by rw [div_def, div_def, map_mul, map_div_by_monic f (monic_mul_leading_coeff_inv hq0)];
  simp [is_ring_hom.map_inv f, leading_coeff, coeff_map f]

lemma map_mod [field k] (f : R →+* k) :
  (p % q).map f = p.map f % q.map f :=
if hq0 : q = 0 then by simp [hq0]
else by rw [mod_def, mod_def, leading_coeff_map f, ← is_ring_hom.map_inv f, ← map_C f,
  ← map_mul f, map_mod_by_monic f (monic_mul_leading_coeff_inv hq0)]

@[simp] lemma map_eq_zero [field k] (f : R →+* k) :
  p.map f = 0 ↔ p = 0 :=
by simp [polynomial.ext_iff, is_ring_hom.map_eq_zero f, coeff_map]

lemma exists_root_of_degree_eq_one (h : degree p = 1) : ∃ x, is_root p x :=
⟨-(p.coeff 0 / p.coeff 1),
  have p.coeff 1 ≠ 0,
    by rw ← nat_degree_eq_of_degree_eq_some h;
    exact mt leading_coeff_eq_zero.1 (λ h0, by simpa [h0] using h),
  by conv in p { rw [eq_X_add_C_of_degree_le_one (show degree p ≤ 1, by rw h; exact le_refl _)] };
    simp [is_root, mul_div_cancel' _ this]⟩

lemma coeff_inv_units (u : units (polynomial R)) (n : ℕ) :
  ((↑u : polynomial R).coeff n)⁻¹ = ((↑u⁻¹ : polynomial R).coeff n) :=
begin
  rw [eq_C_of_degree_eq_zero (degree_coe_units u), eq_C_of_degree_eq_zero (degree_coe_units u⁻¹),
    coeff_C, coeff_C, inv_eq_one_div],
  split_ifs,
  { rw [div_eq_iff_mul_eq (coeff_coe_units_zero_ne_zero u), coeff_zero_eq_eval_zero,
      coeff_zero_eq_eval_zero, ← eval_mul, ← units.coe_mul, inv_mul_self];
    simp },
  { simp }
end

instance : normalization_domain (polynomial R) :=
{ norm_unit := λ p, if hp0 : p = 0 then 1
    else ⟨C p.leading_coeff⁻¹, C p.leading_coeff,
      by rw [← C_mul, inv_mul_cancel, C_1];
       exact mt leading_coeff_eq_zero.1 hp0,
      by rw [← C_mul, mul_inv_cancel, C_1];
       exact mt leading_coeff_eq_zero.1 hp0,⟩,
  norm_unit_zero := dif_pos rfl,
  norm_unit_mul := λ p q hp0 hq0, begin
      rw [dif_neg hp0, dif_neg hq0, dif_neg (mul_ne_zero hp0 hq0)],
      apply units.ext,
      show C (leading_coeff (p * q))⁻¹ = C (leading_coeff p)⁻¹ * C (leading_coeff q)⁻¹,
      rw [leading_coeff_mul, mul_inv', C_mul, mul_comm]
    end,
  norm_unit_coe_units := λ u,
    have hu : degree ↑u⁻¹ = 0, from degree_eq_zero_of_is_unit ⟨u⁻¹, rfl⟩,
    begin
      apply units.ext,
      rw [dif_neg (units.coe_ne_zero u)],
      conv_rhs {rw eq_C_of_degree_eq_zero hu},
      refine C_inj.2 _,
      rw [← nat_degree_eq_of_degree_eq_some hu, leading_coeff,
        coeff_inv_units],
      simp
    end,
  ..polynomial.integral_domain }

lemma monic_normalize (hp0 : p ≠ 0) : monic (normalize p) :=
show leading_coeff (p * ↑(dite _ _ _)) = 1,
by rw dif_neg hp0; exact monic_mul_leading_coeff_inv hp0

lemma coe_norm_unit (hp : p ≠ 0) : (norm_unit p : polynomial R) = C p.leading_coeff⁻¹ :=
show ↑(dite _ _ _) = C p.leading_coeff⁻¹, by rw dif_neg hp; refl

@[simp] lemma degree_normalize : degree (normalize p) = degree p :=
if hp0 : p = 0 then by simp [hp0]
else by rw [normalize, degree_mul_eq, degree_eq_zero_of_is_unit (is_unit_unit _), add_zero]

lemma prime_of_degree_eq_one (hp1 : degree p = 1) : prime p :=
have prime (normalize p),
  from prime_of_degree_eq_one_of_monic (hp1 ▸ degree_normalize)
    (monic_normalize (λ hp0, absurd hp1 (hp0.symm ▸ by simp; exact dec_trivial))),
prime_of_associated normalize_associated this

lemma irreducible_of_degree_eq_one (hp1 : degree p = 1) : irreducible p :=
irreducible_of_prime (prime_of_degree_eq_one hp1)

end field

section derivative
variables [comm_semiring R]

/-- `derivative p` is the formal derivative of the polynomial `p` -/
def derivative (p : polynomial R) : polynomial R := p.sum (λn a, C (a * n) * X^(n - 1))

lemma coeff_derivative (p : polynomial R) (n : ℕ) :
  coeff (derivative p) n = coeff p (n + 1) * (n + 1) :=
begin
  rw [derivative],
  simp only [coeff_X_pow, coeff_sum, coeff_C_mul],
  rw [finsupp.sum, finset.sum_eq_single (n + 1), apply_eq_coeff],
  { rw [if_pos (nat.add_sub_cancel _ _).symm, mul_one, nat.cast_add, nat.cast_one] },
  { assume b, cases b,
    { intros, rw [nat.cast_zero, mul_zero, zero_mul] },
    { intros _ H, rw [nat.succ_sub_one b, if_neg (mt (congr_arg nat.succ) H.symm), mul_zero] } },
  { intro H, rw [not_mem_support_iff.1 H, zero_mul, zero_mul] }
end

@[simp] lemma derivative_zero : derivative (0 : polynomial R) = 0 :=
finsupp.sum_zero_index

lemma derivative_monomial (a : R) (n : ℕ) : derivative (C a * X ^ n) = C (a * n) * X^(n - 1) :=
by rw [← single_eq_C_mul_X, ← single_eq_C_mul_X, derivative, sum_single_index, single_eq_C_mul_X];
  simp only [zero_mul, C_0]; refl

@[simp] lemma derivative_C {a : R} : derivative (C a) = 0 :=
suffices derivative (C a * X^0) = C (a * 0:R) * X ^ 0,
  by simpa only [mul_one, zero_mul, C_0, mul_zero, pow_zero],
derivative_monomial a 0

@[simp] lemma derivative_X : derivative (X : polynomial R) = 1 :=
suffices derivative (C (1:R) * X^1) = C (1 * (1:ℕ)) * X ^ 0,
  by simpa only [mul_one, one_mul, C_1, pow_one, nat.cast_one, pow_zero],
derivative_monomial 1 1

@[simp] lemma derivative_one : derivative (1 : polynomial R) = 0 :=
derivative_C

@[simp] lemma derivative_add {f g : polynomial R} :
  derivative (f + g) = derivative f + derivative g :=
by refine finsupp.sum_add_index _ _; intros;
simp only [add_mul, zero_mul, C_0, C_add, C_mul]

/-- The formal derivative of polynomials, as additive homomorphism. -/
def derivative_hom (R : Type*) [comm_semiring R] : polynomial R →+ polynomial R :=
{ to_fun := derivative,
  map_zero' := derivative_zero,
  map_add' := λ p q, derivative_add }

@[simp] lemma derivative_neg {R : Type*} [comm_ring R] (f : polynomial R) :
  derivative (-f) = -derivative f :=
(derivative_hom R).map_neg f

@[simp] lemma derivative_sub {R : Type*} [comm_ring R] (f g : polynomial R) :
  derivative (f - g) = derivative f - derivative g :=
(derivative_hom R).map_sub f g

instance : is_add_monoid_hom (derivative : polynomial R → polynomial R) :=
(derivative_hom R).is_add_monoid_hom

@[simp] lemma derivative_sum {s : finset ι} {f : ι → polynomial R} :
  derivative (s.sum f) = s.sum (λb, derivative (f b)) :=
(derivative_hom R).map_sum f s

@[simp] lemma derivative_mul {f g : polynomial R} :
  derivative (f * g) = derivative f * g + f * derivative g :=
calc derivative (f * g) = f.sum (λn a, g.sum (λm b, C ((a * b) * (n + m : ℕ)) * X^((n + m) - 1))) :
  begin
    transitivity, exact derivative_sum,
    transitivity, { apply finset.sum_congr rfl, assume x hx, exact derivative_sum },
    apply finset.sum_congr rfl, assume n hn, apply finset.sum_congr rfl, assume m hm,
    transitivity,
    { apply congr_arg, exact single_eq_C_mul_X },
    exact derivative_monomial _ _
  end
  ... = f.sum (λn a, g.sum (λm b,
      (C (a * n) * X^(n - 1)) * (C b * X^m) + (C a * X^n) * (C (b * m) * X^(m - 1)))) :
    sum_congr rfl $ assume n hn, sum_congr rfl $ assume m hm,
      by simp only [nat.cast_add, mul_add, add_mul, C_add, C_mul];
      cases n; simp only [nat.succ_sub_succ, pow_zero];
      cases m; simp only [nat.cast_zero, C_0, nat.succ_sub_succ, zero_mul, mul_zero,
        nat.sub_zero, pow_zero, pow_add, one_mul, pow_succ, mul_comm, mul_left_comm]
  ... = derivative f * g + f * derivative g :
    begin
      conv { to_rhs, congr,
        { rw [← sum_C_mul_X_eq g] },
        { rw [← sum_C_mul_X_eq f] } },
      unfold derivative finsupp.sum,
      simp only [sum_add_distrib, finset.mul_sum, finset.sum_mul]
    end

lemma derivative_eval (p : polynomial R) (x : R) :
  p.derivative.eval x = p.sum (λ n a, (a * n)*x^(n-1)) :=
by simp [derivative, eval_sum, eval_pow]

@[simp] lemma derivative_smul (r : R) (p : polynomial R) : derivative (r • p) = r • derivative p :=
by { ext, simp only [coeff_derivative, mul_assoc, coeff_smul], }

/-- The formal derivative of polynomials, as linear homomorphism. -/
def derivative_lhom (R : Type*) [comm_ring R] : polynomial R →ₗ[R] polynomial R :=
{ to_fun := derivative,
  add    := λ p q, derivative_add,
  smul   := λ r p, derivative_smul r p }

/-- If `f` is a polynomial over a field, and `a : K` satisfies `f' a ≠ 0`,
then `f / (X - a)` is coprime with `X - a`.
Note that we do not assume `f a = 0`, because `f / (X - a) = (f - f a) / (X - a)`. -/
lemma is_coprime_of_is_root_of_eval_derivative_ne_zero {K : Type*} [field K]
  (f : polynomial K) (a : K) (hf' : f.derivative.eval a ≠ 0) :
  ideal.is_coprime (X - C a : polynomial K) (f /ₘ (X - C a)) :=
begin
  refine or.resolve_left (dvd_or_coprime (X - C a) (f /ₘ (X - C a))
    (irreducible_of_degree_eq_one (polynomial.degree_X_sub_C a))) _,
  contrapose! hf' with h,
  have key : (X - C a) * (f /ₘ (X - C a)) = f - (f %ₘ (X - C a)),
  { rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', mod_by_monic_eq_sub_mul_div],
    exact monic_X_sub_C a },
  replace key := congr_arg derivative key,
  simp only [derivative_X, derivative_mul, one_mul, sub_zero, derivative_sub,
    mod_by_monic_X_sub_C_eq_C_eval, derivative_C] at key,
  have : (X - C a) ∣ derivative f := key ▸ (dvd_add h (dvd_mul_right _ _)),
  rw [← dvd_iff_mod_by_monic_eq_zero (monic_X_sub_C _), mod_by_monic_X_sub_C_eq_C_eval] at this,
  rw [← C_inj, this, C_0],
end

end derivative

section domain
variables [integral_domain R]

lemma mem_support_derivative [char_zero R] (p : polynomial R) (n : ℕ) :
  n ∈ (derivative p).support ↔ n + 1 ∈ p.support :=
suffices (¬(coeff p (n + 1) = 0 ∨ ((n + 1:ℕ) : R) = 0)) ↔ coeff p (n + 1) ≠ 0,
  by simpa only [coeff_derivative, apply_eq_coeff, mem_support_iff, ne.def, mul_eq_zero],
by rw [nat.cast_eq_zero]; simp only [nat.succ_ne_zero, or_false]

@[simp] lemma degree_derivative_eq [char_zero R] (p : polynomial R) (hp : 0 < nat_degree p) :
  degree (derivative p) = (nat_degree p - 1 : ℕ) :=
le_antisymm
  (le_trans (degree_sum_le _ _) $ sup_le $ assume n hn,
    have n ≤ nat_degree p, begin
      rw [← with_bot.coe_le_coe, ← degree_eq_nat_degree],
      { refine le_degree_of_ne_zero _, simpa only [mem_support_iff] using hn },
      { assume h, simpa only [h, support_zero] using hn }
    end,
    le_trans (degree_monomial_le _ _) $ with_bot.coe_le_coe.2 $ nat.sub_le_sub_right this _)
  begin
    refine le_sup _,
    rw [mem_support_derivative, nat.sub_add_cancel, mem_support_iff],
    { show ¬ leading_coeff p = 0,
      rw [leading_coeff_eq_zero],
      assume h, rw [h, nat_degree_zero] at hp,
      exact lt_irrefl 0 (lt_of_le_of_lt (zero_le _) hp), },
    exact hp
  end

end domain

section identities

/- @TODO: pow_add_expansion and pow_sub_pow_factor are not specific to polynomials.
  These belong somewhere else. But not in group_power because they depend on tactic.ring

Maybe use data.nat.choose to prove it.
 -/

def pow_add_expansion {R : Type*} [comm_semiring R] (x y : R) : ∀ (n : ℕ),
  {k // (x + y)^n = x^n + n*x^(n-1)*y + k * y^2}
| 0 := ⟨0, by simp⟩
| 1 := ⟨0, by simp⟩
| (n+2) :=
  begin
    cases pow_add_expansion (n+1) with z hz,
    existsi x*z + (n+1)*x^n+z*y,
    calc (x + y) ^ (n + 2) = (x + y) * (x + y) ^ (n + 1) : by ring_exp
    ... = (x + y) * (x ^ (n + 1) + ↑(n + 1) * x ^ (n + 1 - 1) * y + z * y ^ 2) : by rw hz
    ... = x ^ (n + 2) + ↑(n + 2) * x ^ (n + 1) * y + (x*z + (n+1)*x^n+z*y) * y ^ 2 :
      by { push_cast, ring_exp! }
  end

variables [comm_ring R]

private def poly_binom_aux1 (x y : R) (e : ℕ) (a : R) :
  {k : R // a * (x + y)^e = a * (x^e + e*x^(e-1)*y + k*y^2)} :=
begin
  existsi (pow_add_expansion x y e).val,
  congr,
  apply (pow_add_expansion _ _ _).property
end

private lemma poly_binom_aux2 (f : polynomial R) (x y : R) :
  f.eval (x + y) = f.sum (λ e a, a * (x^e + e*x^(e-1)*y + (poly_binom_aux1 x y e a).val*y^2)) :=
begin
  unfold eval eval₂, congr, ext,
  apply (poly_binom_aux1 x y _ _).property
end

private lemma poly_binom_aux3 (f : polynomial R) (x y : R) : f.eval (x + y) =
  f.sum (λ e a, a * x^e) +
  f.sum (λ e a, (a * e * x^(e-1)) * y) +
  f.sum (λ e a, (a *(poly_binom_aux1 x y e a).val)*y^2) :=
by rw poly_binom_aux2; simp [left_distrib, finsupp.sum_add, mul_assoc]

def binom_expansion (f : polynomial R) (x y : R) :
  {k : R // f.eval (x + y) = f.eval x + (f.derivative.eval x) * y + k * y^2} :=
begin
  existsi f.sum (λ e a, a *((poly_binom_aux1 x y e a).val)),
  rw poly_binom_aux3,
  congr,
  { rw derivative_eval, symmetry,
    apply finsupp.sum_mul },
  { symmetry, apply finsupp.sum_mul }
end

def pow_sub_pow_factor (x y : R) : Π (i : ℕ), {z : R // x^i - y^i = z * (x - y)}
| 0 := ⟨0, by simp⟩
| 1 := ⟨1, by simp⟩
| (k+2) :=
  begin
    cases @pow_sub_pow_factor (k+1) with z hz,
    existsi z*x + y^(k+1),
    calc x ^ (k + 2) - y ^ (k + 2)
        = x * (x ^ (k + 1) - y ^ (k + 1)) + (x * y ^ (k + 1) - y ^ (k + 2)) : by ring_exp
    ... = x * (z * (x - y)) + (x * y ^ (k + 1) - y ^ (k + 2)) : by rw hz
    ... = (z * x + y ^ (k + 1)) * (x - y) : by ring_exp
  end

def eval_sub_factor (f : polynomial R) (x y : R) :
  {z : R // f.eval x - f.eval y = z * (x - y)} :=
begin
  refine ⟨f.sum (λ i r, r * (pow_sub_pow_factor x y i).val), _⟩,
  delta eval eval₂,
  rw ← finsupp.sum_sub,
  rw finsupp.sum_mul,
  delta finsupp.sum,
  congr, ext i r, dsimp,
  rw [mul_assoc, ←(pow_sub_pow_factor x y _).property, mul_sub],
end

end identities

end polynomial

namespace is_integral_domain

variables {R : Type*} [comm_ring R]

/-- Lift evidence that `is_integral_domain R` to `is_integral_domain (polynomial R)`. -/
lemma polynomial (h : is_integral_domain R) : is_integral_domain (polynomial R) :=
@integral_domain.to_is_integral_domain _ (@polynomial.integral_domain _ (h.to_integral_domain _))

end is_integral_domain
