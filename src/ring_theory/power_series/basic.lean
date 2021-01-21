/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
import data.mv_polynomial
import ring_theory.algebra_tower
import tactic.linarith

/-!
# Formal power series

This file defines (multivariate) formal power series
and develops the basic properties of these objects.

A formal power series is to a polynomial like an infinite sum is to a finite sum.

We provide the natural inclusion from polynomials to formal power series.

## Generalities

The file starts with setting up the (semi)ring structure on multivariate power series.

`trunc n φ` truncates a formal power series to the polynomial
that has the same coefficients as `φ`, for all `m ≤ n`, and `0` otherwise.

If the constant coefficient of a formal power series is invertible,
then this formal power series is invertible.

Formal power series over a local ring form a local ring.

## Formal power series in one variable

We prove that if the ring of coefficients is an integral domain,
then formal power series in one variable form an integral domain.

The `order` of a formal power series `φ` is the multiplicity of the variable `X` in `φ`.

If the coefficients form an integral domain, then `order` is a valuation
(`order_mul`, `le_order_add`).

## Implementation notes

In this file we define multivariate formal power series with
variables indexed by `σ` and coefficients in `R` as
`mv_power_series σ R := (σ →₀ ℕ) → R`.
Unfortunately there is not yet enough API to show that they are the completion
of the ring of multivariate polynomials. However, we provide most of the infrastructure
that is needed to do this. Once I-adic completion (topological or algebraic) is available
it should not be hard to fill in the details.

Formal power series in one variable are defined as
`power_series R := mv_power_series unit R`.

This allows us to port a lot of proofs and properties
from the multivariate case to the single variable case.
However, it means that formal power series are indexed by `unit →₀ ℕ`,
which is of course canonically isomorphic to `ℕ`.
We then build some glue to treat formal power series as if they are indexed by `ℕ`.
Occasionally this leads to proofs that are uglier than expected.
-/

noncomputable theory
open_locale classical big_operators

/-- Multivariate formal power series, where `σ` is the index set of the variables
and `R` is the coefficient ring.-/
def mv_power_series (σ : Type*) (R : Type*) := (σ →₀ ℕ) → R

namespace mv_power_series
open finsupp
variables {σ R : Type*}

instance [inhabited R]       : inhabited       (mv_power_series σ R) := ⟨λ _, default _⟩
instance [has_zero R]        : has_zero        (mv_power_series σ R) := pi.has_zero
instance [add_monoid R]      : add_monoid      (mv_power_series σ R) := pi.add_monoid
instance [add_group R]       : add_group       (mv_power_series σ R) := pi.add_group
instance [add_comm_monoid R] : add_comm_monoid (mv_power_series σ R) := pi.add_comm_monoid
instance [add_comm_group R]  : add_comm_group  (mv_power_series σ R) := pi.add_comm_group
instance [nontrivial R]      : nontrivial      (mv_power_series σ R) := function.nontrivial

instance {A} [semiring R] [add_comm_monoid A] [semimodule R A] :
  semimodule R (mv_power_series σ A) := pi.semimodule _ _ _

instance {A S} [semiring R] [semiring S] [add_comm_monoid A] [semimodule R A] [semimodule S A]
  [has_scalar R S] [is_scalar_tower R S A] :
  is_scalar_tower R S (mv_power_series σ A) :=
pi.is_scalar_tower

section semiring
variables (R) [semiring R]

/-- The `n`th monomial with coefficient `a` as multivariate formal power series.-/
def monomial (n : σ →₀ ℕ) : R →ₗ[R] mv_power_series σ R :=
linear_map.std_basis R _ n

/-- The `n`th coefficient of a multivariate formal power series.-/
def coeff (n : σ →₀ ℕ) : (mv_power_series σ R) →ₗ[R] R := linear_map.proj n

variables {R}

/-- Two multivariate formal power series are equal if all their coefficients are equal.-/
@[ext] lemma ext {φ ψ} (h : ∀ (n : σ →₀ ℕ), coeff R n φ = coeff R n ψ) :
  φ = ψ :=
funext h

/-- Two multivariate formal power series are equal
 if and only if all their coefficients are equal.-/
lemma ext_iff {φ ψ : mv_power_series σ R} :
  φ = ψ ↔ (∀ (n : σ →₀ ℕ), coeff R n φ = coeff R n ψ) :=
function.funext_iff

lemma coeff_monomial (m n : σ →₀ ℕ) (a : R) :
  coeff R m (monomial R n a) = if m = n then a else 0 :=
by rw [coeff, monomial, linear_map.proj_apply, linear_map.std_basis_apply, function.update_apply,
  pi.zero_apply]

@[simp] lemma coeff_monomial_same (n : σ →₀ ℕ) (a : R) :
  coeff R n (monomial R n a) = a :=
linear_map.std_basis_same _ _ _ _

lemma coeff_monomial_ne {m n : σ →₀ ℕ} (h : m ≠ n) (a : R) :
  coeff R m (monomial R n a) = 0 :=
linear_map.std_basis_ne  _ _ _ _ h a

lemma eq_of_coeff_monomial_ne_zero {m n : σ →₀ ℕ} {a : R} (h : coeff R m (monomial R n a) ≠ 0) :
  m = n :=
by_contra $ λ h', h $ coeff_monomial_ne h' a

@[simp] lemma coeff_comp_monomial (n : σ →₀ ℕ) :
  (coeff R n).comp (monomial R n) = linear_map.id :=
linear_map.ext $ coeff_monomial_same n

@[simp] lemma coeff_zero (n : σ →₀ ℕ) : coeff R n (0 : mv_power_series σ R) = 0 := rfl

variables (m n : σ →₀ ℕ) (φ ψ : mv_power_series σ R)

instance : has_one (mv_power_series σ R) := ⟨monomial R (0 : σ →₀ ℕ) 1⟩

lemma coeff_one :
  coeff R n (1 : mv_power_series σ R) = if n = 0 then 1 else 0 :=
coeff_monomial _ _ _

lemma coeff_zero_one : coeff R (0 : σ →₀ ℕ) 1 = 1 :=
coeff_monomial_same 0 1

lemma monomial_zero_one : monomial R (0 : σ →₀ ℕ) 1 = 1 := rfl

instance : has_mul (mv_power_series σ R) :=
⟨λ φ ψ n, ∑ p in (finsupp.antidiagonal n).support, coeff R p.1 φ * coeff R p.2 ψ⟩

lemma coeff_mul : coeff R n (φ * ψ) =
  ∑ p in (finsupp.antidiagonal n).support, coeff R p.1 φ * coeff R p.2 ψ := rfl

protected lemma zero_mul : (0 : mv_power_series σ R) * φ = 0 :=
ext $ λ n, by simp [coeff_mul]

protected lemma mul_zero : φ * 0 = 0 :=
ext $ λ n, by simp [coeff_mul]

lemma coeff_monomial_mul (a : R) :
  coeff R m (monomial R n a * φ) = if n ≤ m then a * coeff R (m - n) φ else 0 :=
begin
  have : ∀ p ∈ (antidiagonal m).support,
    coeff R (p : (σ →₀ ℕ) × (σ →₀ ℕ)).1 (monomial R n a) * coeff R p.2 φ ≠ 0 → p.1 = n :=
    λ p _ hp, eq_of_coeff_monomial_ne_zero (left_ne_zero_of_mul hp),
  rw [coeff_mul, ← finset.sum_filter_of_ne this, antidiagonal_support_filter_fst_eq,
    finset.sum_ite_index],
  simp only [finset.sum_singleton, coeff_monomial_same, finset.sum_empty]
end

lemma coeff_mul_monomial (a : R) :
  coeff R m (φ * monomial R n a) = if n ≤ m then coeff R (m - n) φ * a else 0 :=
begin
  have : ∀ p ∈ (antidiagonal m).support,
    coeff R (p : (σ →₀ ℕ) × (σ →₀ ℕ)).1 φ * coeff R p.2 (monomial R n a) ≠ 0 → p.2 = n :=
    λ p _ hp, eq_of_coeff_monomial_ne_zero (right_ne_zero_of_mul hp),
  rw [coeff_mul, ← finset.sum_filter_of_ne this, antidiagonal_support_filter_snd_eq,
    finset.sum_ite_index],
  simp only [finset.sum_singleton, coeff_monomial_same, finset.sum_empty]
end

lemma coeff_add_monomial_mul (a : R) :
  coeff R (m + n) (monomial R m a * φ) = a * coeff R n φ :=
begin
  rw [coeff_monomial_mul, if_pos, nat_add_sub_cancel_left],
  exact le_add_right le_rfl
end

lemma coeff_add_mul_monomial (a : R) :
  coeff R (m + n) (φ * monomial R n a) = coeff R m φ * a :=
begin
  rw [coeff_mul_monomial, if_pos, nat_add_sub_cancel],
  exact le_add_left le_rfl
end

protected lemma one_mul : (1 : mv_power_series σ R) * φ = φ :=
ext $ λ n, by simpa using coeff_add_monomial_mul 0 n φ 1

protected lemma mul_one : φ * 1 = φ :=
ext $ λ n, by simpa using coeff_add_mul_monomial n 0 φ 1

protected lemma mul_add (φ₁ φ₂ φ₃ : mv_power_series σ R) :
  φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃ :=
ext $ λ n, by simp only [coeff_mul, mul_add, finset.sum_add_distrib, linear_map.map_add]

protected lemma add_mul (φ₁ φ₂ φ₃ : mv_power_series σ R) :
  (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃ :=
ext $ λ n, by simp only [coeff_mul, add_mul, finset.sum_add_distrib, linear_map.map_add]

protected lemma mul_assoc (φ₁ φ₂ φ₃ : mv_power_series σ R) :
  (φ₁ * φ₂) * φ₃ = φ₁ * (φ₂ * φ₃) :=
begin
  ext1 n,
  simp only [coeff_mul, finset.sum_mul, finset.mul_sum, finset.sum_sigma'],
  refine finset.sum_bij (λ p _, ⟨(p.2.1, p.2.2 + p.1.2), (p.2.2, p.1.2)⟩) _ _ _ _;
    simp only [mem_antidiagonal_support, finset.mem_sigma, heq_iff_eq, prod.mk.inj_iff, and_imp,
      exists_prop],
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩, dsimp only, rintro rfl rfl,
    simp [add_assoc] },
  { rintros ⟨⟨a, b⟩, ⟨c, d⟩⟩, dsimp only, rintro rfl rfl,
    apply mul_assoc },
  { rintros ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨i, j⟩, ⟨k, l⟩⟩, dsimp only, rintro rfl rfl - rfl rfl - rfl rfl,
    refl },
  { rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩, dsimp only, rintro rfl rfl,
    refine ⟨⟨(i + k, l), (i, k)⟩, _, _⟩; simp [add_assoc] }
end

instance : semiring (mv_power_series σ R) :=
{ mul_one := mv_power_series.mul_one,
  one_mul := mv_power_series.one_mul,
  mul_assoc := mv_power_series.mul_assoc,
  mul_zero := mv_power_series.mul_zero,
  zero_mul := mv_power_series.zero_mul,
  left_distrib := mv_power_series.mul_add,
  right_distrib := mv_power_series.add_mul,
  .. mv_power_series.has_one,
  .. mv_power_series.has_mul,
  .. mv_power_series.add_comm_monoid }

end semiring

instance [comm_semiring R] : comm_semiring (mv_power_series σ R) :=
{ mul_comm := λ φ ψ, ext $ λ n, by simpa only [coeff_mul, mul_comm]
    using sum_antidiagonal_support_swap n (λ a b, coeff R a φ * coeff R b ψ),
  .. mv_power_series.semiring }

instance [ring R] : ring (mv_power_series σ R) :=
{ .. mv_power_series.semiring,
  .. mv_power_series.add_comm_group }

instance [comm_ring R] : comm_ring (mv_power_series σ R) :=
{ .. mv_power_series.comm_semiring,
  .. mv_power_series.add_comm_group }

section semiring
variables [semiring R]

lemma monomial_mul_monomial (m n : σ →₀ ℕ) (a b : R) :
  monomial R m a * monomial R n b = monomial R (m + n) (a * b) :=
begin
  ext k,
  simp only [coeff_mul_monomial, coeff_monomial],
  split_ifs with h₁ h₂ h₃ h₃ h₂; try { refl },
  { rw [← h₂, nat_sub_add_cancel h₁] at h₃, exact (h₃ rfl).elim },
  { rw [h₃, nat_add_sub_cancel] at h₂, exact (h₂ rfl).elim },
  { exact zero_mul b },
  { rw h₂ at h₁, exact (h₁ $ le_add_left le_rfl).elim }
end

variables (σ) (R)

/-- The constant multivariate formal power series.-/
def C : R →+* mv_power_series σ R :=
{ map_one' := rfl,
  map_mul' := λ a b, (monomial_mul_monomial 0 0 a b).symm,
  map_zero' := (monomial R (0 : _)).map_zero,
  .. monomial R (0 : σ →₀ ℕ) }

variables {σ} {R}

@[simp] lemma monomial_zero_eq_C : ⇑(monomial R (0 : σ →₀ ℕ)) = C σ R := rfl

lemma monomial_zero_eq_C_apply (a : R) : monomial R (0 : σ →₀ ℕ) a = C σ R a := rfl

lemma coeff_C (n : σ →₀ ℕ) (a : R) :
  coeff R n (C σ R a) = if n = 0 then a else 0 :=
coeff_monomial _ _ _

lemma coeff_zero_C (a : R) : coeff R (0 : σ →₀ℕ) (C σ R a) = a :=
coeff_monomial_same 0 a

/-- The variables of the multivariate formal power series ring.-/
def X (s : σ) : mv_power_series σ R := monomial R (single s 1) 1

lemma coeff_X (n : σ →₀ ℕ) (s : σ) :
  coeff R n (X s : mv_power_series σ R) = if n = (single s 1) then 1 else 0 :=
coeff_monomial _ _ _

lemma coeff_index_single_X (s t : σ) :
  coeff R (single t 1) (X s : mv_power_series σ R) = if t = s then 1 else 0 :=
by { simp only [coeff_X, single_left_inj one_ne_zero], split_ifs; refl }

@[simp] lemma coeff_index_single_self_X (s : σ) :
  coeff R (single s 1) (X s : mv_power_series σ R) = 1 :=
coeff_monomial_same _ _

lemma coeff_zero_X (s : σ) : coeff R (0 : σ →₀ ℕ) (X s : mv_power_series σ R) = 0 :=
by { rw [coeff_X, if_neg], intro h, exact one_ne_zero (single_eq_zero.mp h.symm) }

lemma X_def (s : σ) : X s = monomial R (single s 1) 1 := rfl

lemma X_pow_eq (s : σ) (n : ℕ) :
  (X s : mv_power_series σ R)^n = monomial R (single s n) 1 :=
begin
  induction n with n ih,
  { rw [pow_zero, finsupp.single_zero, monomial_zero_one] },
  { rw [pow_succ', ih, nat.succ_eq_add_one, finsupp.single_add, X, monomial_mul_monomial, one_mul] }
end

lemma coeff_X_pow (m : σ →₀ ℕ) (s : σ) (n : ℕ) :
  coeff R m ((X s : mv_power_series σ R)^n) = if m = single s n then 1 else 0 :=
by rw [X_pow_eq s n, coeff_monomial]

@[simp] lemma coeff_mul_C (n : σ →₀ ℕ) (φ : mv_power_series σ R) (a : R) :
  coeff R n (φ * C σ R a) = coeff R n φ * a :=
by simpa using coeff_add_mul_monomial n 0 φ a

@[simp] lemma coeff_C_mul (n : σ →₀ ℕ) (φ : mv_power_series σ R) (a : R) :
  coeff R n (C σ R a * φ) = a * coeff R n φ :=
by simpa using coeff_add_monomial_mul 0 n φ a

lemma coeff_zero_mul_X (φ : mv_power_series σ R) (s : σ) :
  coeff R (0 : σ →₀ ℕ) (φ * X s) = 0 :=
begin
  have : ¬single s 1 ≤ 0, from λ h, by simpa using h s,
  simp only [X, coeff_mul_monomial, if_neg this]
end

variables (σ) (R)

/-- The constant coefficient of a formal power series.-/
def constant_coeff : (mv_power_series σ R) →+* R :=
{ to_fun := coeff R (0 : σ →₀ ℕ),
  map_one' := coeff_zero_one,
  map_mul' := λ φ ψ, by simp [coeff_mul, support_single_ne_zero],
  map_zero' := linear_map.map_zero _,
  .. coeff R (0 : σ →₀ ℕ) }

variables {σ} {R}

@[simp] lemma coeff_zero_eq_constant_coeff :
  ⇑(coeff R (0 : σ →₀ ℕ)) = constant_coeff σ R := rfl

lemma coeff_zero_eq_constant_coeff_apply (φ : mv_power_series σ R) :
  coeff R (0 : σ →₀ ℕ) φ = constant_coeff σ R φ := rfl

@[simp] lemma constant_coeff_C (a : R) : constant_coeff σ R (C σ R a) = a := rfl
@[simp] lemma constant_coeff_comp_C :
  (constant_coeff σ R).comp (C σ R) = ring_hom.id R := rfl

@[simp] lemma constant_coeff_zero : constant_coeff σ R 0 = 0 := rfl
@[simp] lemma constant_coeff_one : constant_coeff σ R 1 = 1 := rfl
@[simp] lemma constant_coeff_X (s : σ) : constant_coeff σ R (X s) = 0 := coeff_zero_X s

/-- If a multivariate formal power series is invertible,
 then so is its constant coefficient.-/
lemma is_unit_constant_coeff (φ : mv_power_series σ R) (h : is_unit φ) :
  is_unit (constant_coeff σ R φ) :=
h.map' (constant_coeff σ R)

@[simp]
lemma coeff_smul (f : mv_power_series σ R) (n) (a : R) :
  coeff _ n (a • f) = a * coeff _ n f :=
rfl

lemma X_inj [nontrivial R] {s t : σ} : (X s : mv_power_series σ R) = X t ↔ s = t :=
⟨begin
  intro h, replace h := congr_arg (coeff R (single s 1)) h, rw [coeff_X, if_pos rfl, coeff_X] at h,
  split_ifs at h with H,
  { rw finsupp.single_eq_single_iff at H,
    cases H, { exact H.1 }, { exfalso, exact one_ne_zero H.1 } },
  { exfalso, exact one_ne_zero h }
end, congr_arg X⟩

end semiring

section map
variables {S T : Type*} [semiring R] [semiring S] [semiring T]
variables (f : R →+* S) (g : S →+* T)

variable (σ)

/-- The map between multivariate formal power series induced by a map on the coefficients.-/
def map : mv_power_series σ R →+* mv_power_series σ S :=
{ to_fun := λ φ n, f $ coeff R n φ,
  map_zero' := ext $ λ n, f.map_zero,
  map_one' := ext $ λ n, show f ((coeff R n) 1) = (coeff S n) 1,
    by { rw [coeff_one, coeff_one], split_ifs; simp [f.map_one, f.map_zero] },
  map_add' := λ φ ψ, ext $ λ n,
    show f ((coeff R n) (φ + ψ)) = f ((coeff R n) φ) + f ((coeff R n) ψ), by simp,
  map_mul' := λ φ ψ, ext $ λ n, show f _ = _,
  begin
    rw [coeff_mul, ← finset.sum_hom _ f, coeff_mul, finset.sum_congr rfl],
    rintros ⟨i,j⟩ hij, rw [f.map_mul], refl,
  end }

variable {σ}

@[simp] lemma map_id : map σ (ring_hom.id R) = ring_hom.id _ := rfl

lemma map_comp : map σ (g.comp f) = (map σ g).comp (map σ f) := rfl

@[simp] lemma coeff_map (n : σ →₀ ℕ) (φ : mv_power_series σ R) :
  coeff S n (map σ f φ) = f (coeff R n φ) := rfl

@[simp] lemma constant_coeff_map (φ : mv_power_series σ R) :
  constant_coeff σ S (map σ f φ) = f (constant_coeff σ R φ) := rfl

@[simp] lemma map_monomial (n : σ →₀ ℕ) (a : R) :
  map σ f (monomial R n a) = monomial S n (f a) :=
by { ext m, simp [coeff_monomial, apply_ite f] }

@[simp] lemma map_C (a : R) : map σ f (C σ R a) = C σ S (f a) :=
map_monomial _ _ _

@[simp] lemma map_X (s : σ) : map σ f (X s) = X s := by simp [X]

end map

instance {A} [comm_semiring R] [semiring A] [algebra R A] : algebra R (mv_power_series σ A) :=
{ commutes' := λ a φ, by { ext n, simp [algebra.commutes] },
  smul_def' := λ a σ, by { ext n, simp [(coeff A n).map_smul_of_tower a, algebra.smul_def] },
  to_ring_hom := (mv_power_series.map σ (algebra_map R A)).comp (C σ R),
  .. mv_power_series.semimodule }

section trunc
variables [comm_semiring R] (n : σ →₀ ℕ)

/-- Auxiliary definition for the truncation function. -/
def trunc_fun (φ : mv_power_series σ R) : mv_polynomial σ R :=
{ support := (n.antidiagonal.support.image prod.fst).filter (λ m, coeff R m φ ≠ 0),
  to_fun := λ m, if m ≤ n then coeff R m φ else 0,
  mem_support_to_fun := λ m,
  begin
    suffices : m ∈ finset.image prod.fst ((antidiagonal n).support) ↔ m ≤ n,
    { rw [finset.mem_filter, this], split,
      { intro h, rw [if_pos h.1], exact h.2 },
      { intro h, split_ifs at h with H H,
        { exact ⟨H, h⟩ },
        { exfalso, exact h rfl } } },
    rw finset.mem_image, split,
    { rintros ⟨⟨i,j⟩, h, rfl⟩ s,
      rw finsupp.mem_antidiagonal_support at h,
      rw ← h, exact nat.le_add_right _ _ },
    { intro h, refine ⟨(m, n-m), _, rfl⟩,
      rw finsupp.mem_antidiagonal_support, ext s, exact nat.add_sub_of_le (h s) }
  end }

variable (R)

/-- The `n`th truncation of a multivariate formal power series to a multivariate polynomial -/
def trunc : mv_power_series σ R →+ mv_polynomial σ R :=
{ to_fun := trunc_fun n,
  map_zero' := mv_polynomial.ext _ _ $ λ m, by { change ite _ _ _ = _, split_ifs; refl },
  map_add' := λ φ ψ, mv_polynomial.ext _ _ $ λ m,
  begin
    rw mv_polynomial.coeff_add,
    change ite _ _ _ = ite _ _ _ + ite _ _ _,
    split_ifs with H, {refl}, {rw [zero_add]}
  end }

variable {R}

lemma coeff_trunc (m : σ →₀ ℕ) (φ : mv_power_series σ R) :
  mv_polynomial.coeff m (trunc R n φ) =
  if m ≤ n then coeff R m φ else 0 := rfl

@[simp] lemma trunc_one : trunc R n 1 = 1 :=
mv_polynomial.ext _ _ $ λ m,
begin
  rw [coeff_trunc, coeff_one],
  split_ifs with H H' H',
  { subst m, erw mv_polynomial.coeff_C 0, simp },
  { symmetry, erw mv_polynomial.coeff_monomial, convert if_neg (ne.elim (ne.symm H')), },
  { symmetry, erw mv_polynomial.coeff_monomial, convert if_neg _,
    intro H', apply H, subst m, intro s, exact nat.zero_le _ }
end

@[simp] lemma trunc_C (a : R) : trunc R n (C σ R a) = mv_polynomial.C a :=
mv_polynomial.ext _ _ $ λ m,
begin
  rw [coeff_trunc, coeff_C, mv_polynomial.coeff_C],
  split_ifs with H; refl <|> try {simp * at *},
  exfalso, apply H, subst m, intro s, exact nat.zero_le _
end

end trunc

section comm_semiring
variable [comm_semiring R]

lemma X_pow_dvd_iff {s : σ} {n : ℕ} {φ : mv_power_series σ R} :
  (X s : mv_power_series σ R)^n ∣ φ ↔ ∀ m : σ →₀ ℕ, m s < n → coeff R m φ = 0 :=
begin
  split,
  { rintros ⟨φ, rfl⟩ m h,
    rw [coeff_mul, finset.sum_eq_zero],
    rintros ⟨i,j⟩ hij, rw [coeff_X_pow, if_neg, zero_mul],
    contrapose! h, subst i, rw finsupp.mem_antidiagonal_support at hij,
    rw [← hij, finsupp.add_apply, finsupp.single_eq_same], exact nat.le_add_right n _ },
  { intro h, refine ⟨λ m, coeff R (m + (single s n)) φ, _⟩,
    ext m, by_cases H : m - single s n + single s n = m,
    { rw [coeff_mul, finset.sum_eq_single (single s n, m - single s n)],
      { rw [coeff_X_pow, if_pos rfl, one_mul],
        simpa using congr_arg (λ (m : σ →₀ ℕ), coeff R m φ) H.symm },
      { rintros ⟨i,j⟩ hij hne, rw finsupp.mem_antidiagonal_support at hij,
        rw coeff_X_pow, split_ifs with hi,
        { exfalso, apply hne, rw [← hij, ← hi, prod.mk.inj_iff], refine ⟨rfl, _⟩,
          ext t, simp only [nat.add_sub_cancel_left, finsupp.add_apply, finsupp.nat_sub_apply] },
        { exact zero_mul _ } },
        { intro hni, exfalso, apply hni, rwa [finsupp.mem_antidiagonal_support, add_comm] } },
    { rw [h, coeff_mul, finset.sum_eq_zero],
      { rintros ⟨i,j⟩ hij, rw finsupp.mem_antidiagonal_support at hij,
        rw coeff_X_pow, split_ifs with hi,
        { exfalso, apply H, rw [← hij, hi], ext, simp, cc },
        { exact zero_mul _ } },
      { classical, contrapose! H, ext t,
        by_cases hst : s = t,
        { subst t, simpa using nat.sub_add_cancel H },
        { simp [finsupp.single_apply, hst] } } } }
end

lemma X_dvd_iff {s : σ} {φ : mv_power_series σ R} :
  (X s : mv_power_series σ R) ∣ φ ↔ ∀ m : σ →₀ ℕ, m s = 0 → coeff R m φ = 0 :=
begin
  rw [← pow_one (X s : mv_power_series σ R), X_pow_dvd_iff],
  split; intros h m hm,
  { exact h m (hm.symm ▸ zero_lt_one) },
  { exact h m (nat.eq_zero_of_le_zero $ nat.le_of_succ_le_succ hm) }
end
end comm_semiring

section ring
variables [ring R]

/-
The inverse of a multivariate formal power series is defined by
well-founded recursion on the coeffients of the inverse.
-/

/-- Auxiliary definition that unifies
 the totalised inverse formal power series `(_)⁻¹` and
 the inverse formal power series that depends on
 an inverse of the constant coefficient `inv_of_unit`.-/
protected noncomputable def inv.aux (a : R) (φ : mv_power_series σ R) : mv_power_series σ R
| n := if n = 0 then a else
- a * ∑ x in n.antidiagonal.support,
    if h : x.2 < n then coeff R x.1 φ * inv.aux x.2 else 0
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨_, finsupp.lt_wf σ⟩],
  dec_tac := tactic.assumption }

lemma coeff_inv_aux (n : σ →₀ ℕ) (a : R) (φ : mv_power_series σ R) :
  coeff R n (inv.aux a φ) = if n = 0 then a else
  - a * ∑ x in n.antidiagonal.support,
    if x.2 < n then coeff R x.1 φ * coeff R x.2 (inv.aux a φ) else 0 :=
show inv.aux a φ n = _, by { rw inv.aux, refl }

/-- A multivariate formal power series is invertible if the constant coefficient is invertible.-/
def inv_of_unit (φ : mv_power_series σ R) (u : units R) : mv_power_series σ R :=
inv.aux (↑u⁻¹) φ

lemma coeff_inv_of_unit (n : σ →₀ ℕ) (φ : mv_power_series σ R) (u : units R) :
  coeff R n (inv_of_unit φ u) = if n = 0 then ↑u⁻¹ else
  - ↑u⁻¹ * ∑ x in n.antidiagonal.support,
    if x.2 < n then coeff R x.1 φ * coeff R x.2 (inv_of_unit φ u) else 0 :=
coeff_inv_aux n (↑u⁻¹) φ

@[simp] lemma constant_coeff_inv_of_unit (φ : mv_power_series σ R) (u : units R) :
  constant_coeff σ R (inv_of_unit φ u) = ↑u⁻¹ :=
by rw [← coeff_zero_eq_constant_coeff_apply, coeff_inv_of_unit, if_pos rfl]

lemma mul_inv_of_unit (φ : mv_power_series σ R) (u : units R) (h : constant_coeff σ R φ = u) :
  φ * inv_of_unit φ u = 1 :=
ext $ λ n, if H : n = 0 then by { rw H, simp [coeff_mul, support_single_ne_zero, h], }
else
begin
  have : ((0 : σ →₀ ℕ), n) ∈ n.antidiagonal.support,
  { rw [finsupp.mem_antidiagonal_support, zero_add] },
  rw [coeff_one, if_neg H, coeff_mul,
    ← finset.insert_erase this, finset.sum_insert (finset.not_mem_erase _ _),
    coeff_zero_eq_constant_coeff_apply, h, coeff_inv_of_unit, if_neg H,
    neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, units.mul_inv_cancel_left,
    ← finset.insert_erase this, finset.sum_insert (finset.not_mem_erase _ _),
    finset.insert_erase this, if_neg (not_lt_of_ge $ le_refl _), zero_add, add_comm,
    ← sub_eq_add_neg, sub_eq_zero, finset.sum_congr rfl],
  rintros ⟨i,j⟩ hij, rw [finset.mem_erase, finsupp.mem_antidiagonal_support] at hij,
  cases hij with h₁ h₂,
  subst n, rw if_pos,
  suffices : (0 : _) + j < i + j, {simpa},
  apply add_lt_add_right,
  split,
  { intro s, exact nat.zero_le _ },
  { intro H, apply h₁,
    suffices : i = 0, {simp [this]},
    ext1 s, exact nat.eq_zero_of_le_zero (H s) }
end

end ring

section comm_ring
variable [comm_ring R]

/-- Multivariate formal power series over a local ring form a local ring. -/
instance is_local_ring [local_ring R] : local_ring (mv_power_series σ R) :=
{ is_local := by { intro φ, rcases local_ring.is_local (constant_coeff σ R φ) with ⟨u,h⟩|⟨u,h⟩;
    [left, right];
    { refine is_unit_of_mul_eq_one _ _ (mul_inv_of_unit _ u _),
      simpa using h.symm } } }

-- TODO(jmc): once adic topology lands, show that this is complete

end comm_ring

section local_ring
variables {S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S)
  [is_local_ring_hom f]

-- Thanks to the linter for informing us that  this instance does
-- not actually need R and S to be local rings!

/-- The map `A[[X]] → B[[X]]` induced by a local ring hom `A → B` is local -/
instance map.is_local_ring_hom : is_local_ring_hom (map σ f) :=
⟨begin
  rintros φ ⟨ψ, h⟩,
  replace h := congr_arg (constant_coeff σ S) h,
  rw constant_coeff_map at h,
  have : is_unit (constant_coeff σ S ↑ψ) := @is_unit_constant_coeff σ S _ (↑ψ) (is_unit_unit ψ),
  rw h at this,
  rcases is_unit_of_map_unit f _ this with ⟨c, hc⟩,
  exact is_unit_of_mul_eq_one φ (inv_of_unit φ c) (mul_inv_of_unit φ c hc.symm)
end⟩

variables [local_ring R] [local_ring S]

instance : local_ring (mv_power_series σ R) :=
{ is_local := local_ring.is_local }

end local_ring

section field
variables {k : Type*} [field k]

/-- The inverse `1/f` of a multivariable power series `f` over a field -/
protected def inv (φ : mv_power_series σ k) : mv_power_series σ k :=
inv.aux (constant_coeff σ k φ)⁻¹ φ

instance : has_inv (mv_power_series σ k) := ⟨mv_power_series.inv⟩

lemma coeff_inv (n : σ →₀ ℕ) (φ : mv_power_series σ k) :
  coeff k n (φ⁻¹) = if n = 0 then (constant_coeff σ k φ)⁻¹ else
  - (constant_coeff σ k φ)⁻¹ * ∑ x in n.antidiagonal.support,
    if x.2 < n then coeff k x.1 φ * coeff k x.2 (φ⁻¹) else 0 :=
coeff_inv_aux n _ φ

@[simp] lemma constant_coeff_inv (φ : mv_power_series σ k) :
  constant_coeff σ k (φ⁻¹) = (constant_coeff σ k φ)⁻¹ :=
by rw [← coeff_zero_eq_constant_coeff_apply, coeff_inv, if_pos rfl]

lemma inv_eq_zero {φ : mv_power_series σ k} :
  φ⁻¹ = 0 ↔ constant_coeff σ k φ = 0 :=
⟨λ h, by simpa using congr_arg (constant_coeff σ k) h,
 λ h, ext $ λ n, by { rw coeff_inv, split_ifs;
 simp only [h, mv_power_series.coeff_zero, zero_mul, inv_zero, neg_zero] }⟩

@[simp, priority 1100]
lemma inv_of_unit_eq (φ : mv_power_series σ k) (h : constant_coeff σ k φ ≠ 0) :
  inv_of_unit φ (units.mk0 _ h) = φ⁻¹ := rfl

@[simp]
lemma inv_of_unit_eq' (φ : mv_power_series σ k) (u : units k) (h : constant_coeff σ k φ = u) :
  inv_of_unit φ u = φ⁻¹ :=
begin
  rw ← inv_of_unit_eq φ (h.symm ▸ u.ne_zero),
  congr' 1, rw [units.ext_iff], exact h.symm,
end

@[simp] protected lemma mul_inv (φ : mv_power_series σ k) (h : constant_coeff σ k φ ≠ 0) :
  φ * φ⁻¹ = 1 :=
by rw [← inv_of_unit_eq φ h, mul_inv_of_unit φ (units.mk0 _ h) rfl]

@[simp] protected lemma inv_mul (φ : mv_power_series σ k) (h : constant_coeff σ k φ ≠ 0) :
  φ⁻¹ * φ = 1 :=
by rw [mul_comm, φ.mul_inv h]

protected lemma eq_mul_inv_iff_mul_eq {φ₁ φ₂ φ₃ : mv_power_series σ k}
  (h : constant_coeff σ k φ₃ ≠ 0) :
  φ₁ = φ₂ * φ₃⁻¹ ↔ φ₁ * φ₃ = φ₂ :=
⟨λ k, by simp [k, mul_assoc, mv_power_series.inv_mul _ h],
 λ k, by simp [← k, mul_assoc, mv_power_series.mul_inv _ h]⟩

protected lemma eq_inv_iff_mul_eq_one {φ ψ : mv_power_series σ k} (h : constant_coeff σ k ψ ≠ 0) :
  φ = ψ⁻¹ ↔ φ * ψ = 1 :=
by rw [← mv_power_series.eq_mul_inv_iff_mul_eq h, one_mul]

protected lemma inv_eq_iff_mul_eq_one {φ ψ : mv_power_series σ k} (h : constant_coeff σ k ψ ≠ 0) :
  ψ⁻¹ = φ ↔ φ * ψ = 1 :=
by rw [eq_comm, mv_power_series.eq_inv_iff_mul_eq_one h]

end field

end mv_power_series

namespace mv_polynomial
open finsupp
variables {σ : Type*} {R : Type*} [comm_semiring R]

/-- The natural inclusion from multivariate polynomials into multivariate formal power series.-/
instance coe_to_mv_power_series : has_coe (mv_polynomial σ R) (mv_power_series σ R) :=
⟨λ φ n, coeff n φ⟩

@[simp, norm_cast] lemma coeff_coe (φ : mv_polynomial σ R) (n : σ →₀ ℕ) :
mv_power_series.coeff R n ↑φ = coeff n φ := rfl

@[simp, norm_cast] lemma coe_monomial (n : σ →₀ ℕ) (a : R) :
  (monomial n a : mv_power_series σ R) = mv_power_series.monomial R n a :=
mv_power_series.ext $ λ m,
begin
  rw [coeff_coe, coeff_monomial, mv_power_series.coeff_monomial],
  split_ifs with h₁ h₂; refl <|> subst m; contradiction
end

@[simp, norm_cast] lemma coe_zero : ((0 : mv_polynomial σ R) : mv_power_series σ R) = 0 := rfl

@[simp, norm_cast] lemma coe_one : ((1 : mv_polynomial σ R) : mv_power_series σ R) = 1 :=
coe_monomial _ _

@[simp, norm_cast] lemma coe_add (φ ψ : mv_polynomial σ R) :
  ((φ + ψ : mv_polynomial σ R) : mv_power_series σ R) = φ + ψ := rfl

@[simp, norm_cast] lemma coe_mul (φ ψ : mv_polynomial σ R) :
  ((φ * ψ : mv_polynomial σ R) : mv_power_series σ R) = φ * ψ :=
mv_power_series.ext $ λ n,
by simp only [coeff_coe, mv_power_series.coeff_mul, coeff_mul]

@[simp, norm_cast] lemma coe_C (a : R) :
  ((C a : mv_polynomial σ R) : mv_power_series σ R) = mv_power_series.C σ R a :=
coe_monomial _ _

@[simp, norm_cast] lemma coe_X (s : σ) :
  ((X s : mv_polynomial σ R) : mv_power_series σ R) = mv_power_series.X s :=
coe_monomial _ _

/--
The coercion from multivariable polynomials to multivariable power series
as a ring homomorphism.
-/
-- TODO as an algebra homomorphism?
def coe_to_mv_power_series.ring_hom : mv_polynomial σ R →+* mv_power_series σ R :=
{ to_fun := (coe : mv_polynomial σ R → mv_power_series σ R),
  map_zero' := coe_zero,
  map_one' := coe_one,
  map_add' := coe_add,
  map_mul' := coe_mul }

end mv_polynomial

/-- Formal power series over the coefficient ring `R`.-/
def power_series (R : Type*) := mv_power_series unit R

namespace power_series
open finsupp (single)
variable {R : Type*}

section
local attribute [reducible] power_series

instance [inhabited R]       : inhabited       (power_series R) := by apply_instance
instance [add_monoid R]      : add_monoid      (power_series R) := by apply_instance
instance [add_group R]       : add_group       (power_series R) := by apply_instance
instance [add_comm_monoid R] : add_comm_monoid (power_series R) := by apply_instance
instance [add_comm_group R]  : add_comm_group  (power_series R) := by apply_instance
instance [semiring R]        : semiring        (power_series R) := by apply_instance
instance [comm_semiring R]   : comm_semiring   (power_series R) := by apply_instance
instance [ring R]            : ring            (power_series R) := by apply_instance
instance [comm_ring R]       : comm_ring       (power_series R) := by apply_instance
instance [nontrivial R]      : nontrivial      (power_series R) := by apply_instance

instance {A} [semiring R] [add_comm_monoid A] [semimodule R A] :
  semimodule R (power_series A) := by apply_instance

instance {A S} [semiring R] [semiring S] [add_comm_monoid A] [semimodule R A] [semimodule S A]
  [has_scalar R S] [is_scalar_tower R S A] :
  is_scalar_tower R S (power_series A) :=
pi.is_scalar_tower

instance [comm_ring R]       : algebra R       (power_series R) := by apply_instance

end

section semiring
variables (R) [semiring R]

/-- The `n`th coefficient of a formal power series.-/
def coeff (n : ℕ) : power_series R →ₗ[R] R := mv_power_series.coeff R (single () n)

/-- The `n`th monomial with coefficient `a` as formal power series.-/
def monomial (n : ℕ) : R →ₗ[R] power_series R := mv_power_series.monomial R (single () n)

variables {R}

lemma coeff_def {s : unit →₀ ℕ} {n : ℕ} (h : s () = n) :
  coeff R n = mv_power_series.coeff R s :=
by erw [coeff, ← h, ← finsupp.unique_single s]

/-- Two formal power series are equal if all their coefficients are equal.-/
@[ext] lemma ext {φ ψ : power_series R} (h : ∀ n, coeff R n φ = coeff R n ψ) :
  φ = ψ :=
mv_power_series.ext $ λ n,
by { rw ← coeff_def, { apply h }, refl }

/-- Two formal power series are equal if all their coefficients are equal.-/
lemma ext_iff {φ ψ : power_series R} : φ = ψ ↔ (∀ n, coeff R n φ = coeff R n ψ) :=
⟨λ h n, congr_arg (coeff R n) h, ext⟩

/-- Constructor for formal power series.-/
def mk {R} (f : ℕ → R) : power_series R := λ s, f (s ())

@[simp] lemma coeff_mk (n : ℕ) (f : ℕ → R) : coeff R n (mk f) = f n :=
congr_arg f finsupp.single_eq_same

lemma coeff_monomial (m n : ℕ) (a : R) :
  coeff R m (monomial R n a) = if m = n then a else 0 :=
calc coeff R m (monomial R n a) = _ : mv_power_series.coeff_monomial _ _ _
    ... = if m = n then a else 0 :
by { simp only [finsupp.unique_single_eq_iff], split_ifs; refl }

lemma monomial_eq_mk (n : ℕ) (a : R) :
  monomial R n a = mk (λ m, if m = n then a else 0) :=
ext $ λ m, by { rw [coeff_monomial, coeff_mk] }

@[simp] lemma coeff_monomial_same (n : ℕ) (a : R) :
  coeff R n (monomial R n a) = a :=
mv_power_series.coeff_monomial_same _ _

@[simp] lemma coeff_comp_monomial (n : ℕ) :
  (coeff R n).comp (monomial R n) = linear_map.id :=
linear_map.ext $ coeff_monomial_same n

variable (R)

/--The constant coefficient of a formal power series. -/
def constant_coeff : power_series R →+* R := mv_power_series.constant_coeff unit R

/-- The constant formal power series.-/
def C : R →+* power_series R := mv_power_series.C unit R

variable {R}

/-- The variable of the formal power series ring.-/
def X : power_series R := mv_power_series.X ()

@[simp] lemma coeff_zero_eq_constant_coeff :
  ⇑(coeff R 0) = constant_coeff R :=
by { rw [coeff, finsupp.single_zero], refl }

lemma coeff_zero_eq_constant_coeff_apply (φ : power_series R) :
  coeff R 0 φ = constant_coeff R φ :=
by rw [coeff_zero_eq_constant_coeff]; refl

@[simp] lemma monomial_zero_eq_C : ⇑(monomial R 0) = C R :=
by rw [monomial, finsupp.single_zero, mv_power_series.monomial_zero_eq_C, C]

lemma monomial_zero_eq_C_apply (a : R) : monomial R 0 a = C R a :=
by simp

lemma coeff_C (n : ℕ) (a : R) :
  coeff R n (C R a : power_series R) = if n = 0 then a else 0 :=
by rw [← monomial_zero_eq_C_apply, coeff_monomial]

lemma coeff_zero_C (a : R) : coeff R 0 (C R a) = a :=
by rw [← monomial_zero_eq_C_apply, coeff_monomial_same 0 a]

lemma X_eq : (X : power_series R) = monomial R 1 1 := rfl

lemma coeff_X (n : ℕ) :
  coeff R n (X : power_series R) = if n = 1 then 1 else 0 :=
by rw [X_eq, coeff_monomial]

lemma coeff_zero_X : coeff R 0 (X : power_series R) = 0 :=
by rw [coeff, finsupp.single_zero, X, mv_power_series.coeff_zero_X]

@[simp] lemma coeff_one_X : coeff R 1 (X : power_series R) = 1 :=
by rw [coeff_X, if_pos rfl]

lemma X_pow_eq (n : ℕ) : (X : power_series R)^n = monomial R n 1 :=
mv_power_series.X_pow_eq _ n

lemma coeff_X_pow (m n : ℕ) :
  coeff R m ((X : power_series R)^n) = if m = n then 1 else 0 :=
by rw [X_pow_eq, coeff_monomial]

@[simp] lemma coeff_X_pow_self (n : ℕ) :
  coeff R n ((X : power_series R)^n) = 1 :=
by rw [coeff_X_pow, if_pos rfl]

@[simp] lemma coeff_one (n : ℕ) :
  coeff R n (1 : power_series R) = if n = 0 then 1 else 0 :=
calc coeff R n (1 : power_series R) = _ : mv_power_series.coeff_one _
    ... = if n = 0 then 1 else 0 :
by { simp only [finsupp.single_eq_zero], split_ifs; refl }

lemma coeff_zero_one : coeff R 0 (1 : power_series R) = 1 :=
coeff_zero_C 1

lemma coeff_mul (n : ℕ) (φ ψ : power_series R) :
  coeff R n (φ * ψ) = ∑ p in finset.nat.antidiagonal n, coeff R p.1 φ * coeff R p.2 ψ :=
begin
  symmetry,
  apply finset.sum_bij (λ (p : ℕ × ℕ) h, (single () p.1, single () p.2)),
  { rintros ⟨i,j⟩ hij, rw finset.nat.mem_antidiagonal at hij,
    rw [finsupp.mem_antidiagonal_support, ← finsupp.single_add, hij], },
  { rintros ⟨i,j⟩ hij, refl },
  { rintros ⟨i,j⟩ ⟨k,l⟩ hij hkl,
    simpa only [prod.mk.inj_iff, finsupp.unique_single_eq_iff] using id },
  { rintros ⟨f,g⟩ hfg,
    refine ⟨(f (), g ()), _, _⟩,
    { rw finsupp.mem_antidiagonal_support at hfg,
      rw [finset.nat.mem_antidiagonal, ← finsupp.add_apply, hfg, finsupp.single_eq_same] },
    { rw prod.mk.inj_iff, dsimp,
      exact ⟨finsupp.unique_single f, finsupp.unique_single g⟩ } }
end

@[simp] lemma coeff_mul_C (n : ℕ) (φ : power_series R) (a : R) :
  coeff R n (φ * C R a) = coeff R n φ * a :=
mv_power_series.coeff_mul_C _ φ a

@[simp] lemma coeff_C_mul (n : ℕ) (φ : power_series R) (a : R) :
  coeff R n (C R a * φ) = a * coeff R n φ :=
mv_power_series.coeff_C_mul _ φ a

@[simp] lemma coeff_smul (n : ℕ) (φ : power_series R) (a : R) :
  coeff R n (a • φ) = a * coeff R n φ :=
rfl

@[simp] lemma coeff_succ_mul_X (n : ℕ) (φ : power_series R) :
  coeff R (n+1) (φ * X) = coeff R n φ :=
begin
  simp only [coeff, finsupp.single_add],
  convert φ.coeff_add_mul_monomial (single () n) (single () 1) _,
  rw mul_one
end

@[simp] lemma constant_coeff_C (a : R) : constant_coeff R (C R a) = a := rfl
@[simp] lemma constant_coeff_comp_C :
  (constant_coeff R).comp (C R) = ring_hom.id R := rfl

@[simp] lemma constant_coeff_zero : constant_coeff R 0 = 0 := rfl
@[simp] lemma constant_coeff_one : constant_coeff R 1 = 1 := rfl
@[simp] lemma constant_coeff_X : constant_coeff R X = 0 := mv_power_series.coeff_zero_X _

lemma coeff_zero_mul_X (φ : power_series R) : coeff R 0 (φ * X) = 0 := by simp

/-- If a formal power series is invertible, then so is its constant coefficient.-/
lemma is_unit_constant_coeff (φ : power_series R) (h : is_unit φ) :
  is_unit (constant_coeff R φ) :=
mv_power_series.is_unit_constant_coeff φ h

section map
variables {S : Type*} {T : Type*} [semiring S] [semiring T]
variables (f : R →+* S) (g : S →+* T)

/-- The map between formal power series induced by a map on the coefficients.-/
def map : power_series R →+* power_series S :=
mv_power_series.map _ f

@[simp] lemma map_id : (map (ring_hom.id R) :
  power_series R → power_series R) = id := rfl

lemma map_comp : map (g.comp f) = (map g).comp (map f) := rfl

@[simp] lemma coeff_map (n : ℕ) (φ : power_series R) :
  coeff S n (map f φ) = f (coeff R n φ) := rfl

end map

end semiring

section comm_semiring
variables [comm_semiring R]

lemma X_pow_dvd_iff {n : ℕ} {φ : power_series R} :
  (X : power_series R)^n ∣ φ ↔ ∀ m, m < n → coeff R m φ = 0 :=
begin
  convert @mv_power_series.X_pow_dvd_iff unit R _ () n φ, apply propext,
  classical, split; intros h m hm,
  { rw finsupp.unique_single m, convert h _ hm },
  { apply h, simpa only [finsupp.single_eq_same] using hm }
end

lemma X_dvd_iff {φ : power_series R} :
  (X : power_series R) ∣ φ ↔ constant_coeff R φ = 0 :=
begin
  rw [← pow_one (X : power_series R), X_pow_dvd_iff, ← coeff_zero_eq_constant_coeff_apply],
  split; intro h,
  { exact h 0 zero_lt_one },
  { intros m hm, rwa nat.eq_zero_of_le_zero (nat.le_of_succ_le_succ hm) }
end

section trunc

/-- The `n`th truncation of a formal power series to a polynomial -/
def trunc (n : ℕ) (φ : power_series R) : polynomial R :=
{ support := ((finset.nat.antidiagonal n).image prod.fst).filter (λ m, coeff R m φ ≠ 0),
  to_fun := λ m, if m ≤ n then coeff R m φ else 0,
  mem_support_to_fun := λ m,
  begin
    suffices : m ∈ ((finset.nat.antidiagonal n).image prod.fst) ↔ m ≤ n,
    { rw [finset.mem_filter, this], split,
      { intro h, rw [if_pos h.1], exact h.2 },
      { intro h, split_ifs at h with H H,
        { exact ⟨H, h⟩ },
        { exfalso, exact h rfl } } },
    rw finset.mem_image, split,
    { rintros ⟨⟨i,j⟩, h, rfl⟩,
      rw finset.nat.mem_antidiagonal at h,
      rw ← h, exact nat.le_add_right _ _ },
    { intro h, refine ⟨(m, n-m), _, rfl⟩,
      rw finset.nat.mem_antidiagonal, exact nat.add_sub_of_le h }
  end }

lemma coeff_trunc (m) (n) (φ : power_series R) :
  polynomial.coeff (trunc n φ) m = if m ≤ n then coeff R m φ else 0 := rfl

@[simp] lemma trunc_zero (n) : trunc n (0 : power_series R) = 0 :=
polynomial.ext $ λ m,
begin
  rw [coeff_trunc, linear_map.map_zero, polynomial.coeff_zero],
  split_ifs; refl
end

@[simp] lemma trunc_one (n) : trunc n (1 : power_series R) = 1 :=
polynomial.ext $ λ m,
begin
  rw [coeff_trunc, coeff_one],
  split_ifs with H H' H'; rw [polynomial.coeff_one],
  { subst m, rw [if_pos rfl] },
  { symmetry, exact if_neg (ne.elim (ne.symm H')) },
  { symmetry, refine if_neg _,
    intro H', apply H, subst m, exact nat.zero_le _ }
end

@[simp] lemma trunc_C (n) (a : R) : trunc n (C R a) = polynomial.C a :=
polynomial.ext $ λ m,

begin
  rw [coeff_trunc, coeff_C, polynomial.coeff_C],
  split_ifs with H; refl <|> try {simp * at *}
end

@[simp] lemma trunc_add (n) (φ ψ : power_series R) :
  trunc n (φ + ψ) = trunc n φ + trunc n ψ :=
polynomial.ext $ λ m,
begin
  simp only [coeff_trunc, add_monoid_hom.map_add, polynomial.coeff_add],
  split_ifs with H, {refl}, {rw [zero_add]}
end

end trunc

end comm_semiring

section ring
variables [ring R]

/-- Auxiliary function used for computing inverse of a power series -/
protected def inv.aux : R → power_series R → power_series R :=
mv_power_series.inv.aux

lemma coeff_inv_aux (n : ℕ) (a : R) (φ : power_series R) :
  coeff R n (inv.aux a φ) = if n = 0 then a else
  - a * ∑ x in finset.nat.antidiagonal n,
    if x.2 < n then coeff R x.1 φ * coeff R x.2 (inv.aux a φ) else 0 :=
begin
  rw [coeff, inv.aux, mv_power_series.coeff_inv_aux],
  simp only [finsupp.single_eq_zero],
  split_ifs, {refl},
  congr' 1,
  symmetry,
  apply finset.sum_bij (λ (p : ℕ × ℕ) h, (single () p.1, single () p.2)),
  { rintros ⟨i,j⟩ hij, rw finset.nat.mem_antidiagonal at hij,
    rw [finsupp.mem_antidiagonal_support, ← finsupp.single_add, hij], },
  { rintros ⟨i,j⟩ hij,
    by_cases H : j < n,
    { rw [if_pos H, if_pos], {refl},
      split,
      { rintro ⟨⟩, simpa [finsupp.single_eq_same] using le_of_lt H },
      { intro hh, rw lt_iff_not_ge at H, apply H,
        simpa [finsupp.single_eq_same] using hh () } },
    { rw [if_neg H, if_neg], rintro ⟨h₁, h₂⟩, apply h₂, rintro ⟨⟩,
     simpa [finsupp.single_eq_same] using not_lt.1 H } },
  { rintros ⟨i,j⟩ ⟨k,l⟩ hij hkl,
    simpa only [prod.mk.inj_iff, finsupp.unique_single_eq_iff] using id },
  { rintros ⟨f,g⟩ hfg,
    refine ⟨(f (), g ()), _, _⟩,
    { rw finsupp.mem_antidiagonal_support at hfg,
      rw [finset.nat.mem_antidiagonal, ← finsupp.add_apply, hfg, finsupp.single_eq_same] },
    { rw prod.mk.inj_iff, dsimp,
      exact ⟨finsupp.unique_single f, finsupp.unique_single g⟩ } }
end

/-- A formal power series is invertible if the constant coefficient is invertible.-/
def inv_of_unit (φ : power_series R) (u : units R) : power_series R :=
mv_power_series.inv_of_unit φ u

lemma coeff_inv_of_unit (n : ℕ) (φ : power_series R) (u : units R) :
  coeff R n (inv_of_unit φ u) = if n = 0 then ↑u⁻¹ else
  - ↑u⁻¹ * ∑ x in finset.nat.antidiagonal n,
    if x.2 < n then coeff R x.1 φ * coeff R x.2 (inv_of_unit φ u) else 0 :=
coeff_inv_aux n ↑u⁻¹ φ

@[simp] lemma constant_coeff_inv_of_unit (φ : power_series R) (u : units R) :
  constant_coeff R (inv_of_unit φ u) = ↑u⁻¹ :=
by rw [← coeff_zero_eq_constant_coeff_apply, coeff_inv_of_unit, if_pos rfl]

lemma mul_inv_of_unit (φ : power_series R) (u : units R) (h : constant_coeff R φ = u) :
  φ * inv_of_unit φ u = 1 :=
mv_power_series.mul_inv_of_unit φ u $ h

end ring

section integral_domain
variable [integral_domain R]

lemma eq_zero_or_eq_zero_of_mul_eq_zero (φ ψ : power_series R) (h : φ * ψ = 0) :
  φ = 0 ∨ ψ = 0 :=
begin
    rw or_iff_not_imp_left, intro H,
    have ex : ∃ m, coeff R m φ ≠ 0, { contrapose! H, exact ext H },
    let m := nat.find ex,
    have hm₁ : coeff R m φ ≠ 0 := nat.find_spec ex,
    have hm₂ : ∀ k < m, ¬coeff R k φ ≠ 0 := λ k, nat.find_min ex,
    ext n, rw (coeff R n).map_zero, apply nat.strong_induction_on n,
    clear n, intros n ih,
    replace h := congr_arg (coeff R (m + n)) h,
    rw [linear_map.map_zero, coeff_mul, finset.sum_eq_single (m,n)] at h,
    { replace h := eq_zero_or_eq_zero_of_mul_eq_zero h,
      rw or_iff_not_imp_left at h, exact h hm₁ },
    { rintro ⟨i,j⟩ hij hne,
      by_cases hj : j < n, { rw [ih j hj, mul_zero] },
      by_cases hi : i < m,
      { specialize hm₂ _ hi, push_neg at hm₂, rw [hm₂, zero_mul] },
      rw finset.nat.mem_antidiagonal at hij,
      push_neg at hi hj,
      suffices : m < i,
      { have : m + n < i + j := add_lt_add_of_lt_of_le this hj,
        exfalso, exact ne_of_lt this hij.symm },
      contrapose! hne, have : i = m := le_antisymm hne hi, subst i, clear hi hne,
      simpa [ne.def, prod.mk.inj_iff] using (add_right_inj m).mp hij },
    { contrapose!, intro h, rw finset.nat.mem_antidiagonal }
end

instance : integral_domain (power_series R) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero,
  .. power_series.nontrivial,
  .. power_series.comm_ring }

/-- The ideal spanned by the variable in the power series ring
 over an integral domain is a prime ideal.-/
lemma span_X_is_prime : (ideal.span ({X} : set (power_series R))).is_prime :=
begin
  suffices : ideal.span ({X} : set (power_series R)) = (constant_coeff R).ker,
  { rw this, exact ring_hom.ker_is_prime _ },
  apply ideal.ext, intro φ,
  rw [ring_hom.mem_ker, ideal.mem_span_singleton, X_dvd_iff]
end

/-- The variable of the power series ring over an integral domain is prime.-/
lemma X_prime : prime (X : power_series R) :=
begin
  rw ← ideal.span_singleton_prime,
  { exact span_X_is_prime },
  { intro h, simpa using congr_arg (coeff R 1) h }
end

end integral_domain

section local_ring
variables {S : Type*} [comm_ring R] [comm_ring S]
  (f : R →+* S) [is_local_ring_hom f]

instance map.is_local_ring_hom : is_local_ring_hom (map f) :=
mv_power_series.map.is_local_ring_hom f

variables [local_ring R] [local_ring S]

instance : local_ring (power_series R) :=
mv_power_series.local_ring

end local_ring

section field
variables {k : Type*} [field k]

/-- The inverse 1/f of a power series f defined over a field -/
protected def inv : power_series k → power_series k :=
mv_power_series.inv

instance : has_inv (power_series k) := ⟨power_series.inv⟩

lemma inv_eq_inv_aux (φ : power_series k) :
  φ⁻¹ = inv.aux (constant_coeff k φ)⁻¹ φ := rfl

lemma coeff_inv (n) (φ : power_series k) :
  coeff k n (φ⁻¹) = if n = 0 then (constant_coeff k φ)⁻¹ else
  - (constant_coeff k φ)⁻¹ * ∑ x in finset.nat.antidiagonal n,
    if x.2 < n then coeff k x.1 φ * coeff k x.2 (φ⁻¹) else 0 :=
by rw [inv_eq_inv_aux, coeff_inv_aux n (constant_coeff k φ)⁻¹ φ]

@[simp] lemma constant_coeff_inv (φ : power_series k) :
  constant_coeff k (φ⁻¹) = (constant_coeff k φ)⁻¹ :=
mv_power_series.constant_coeff_inv φ

lemma inv_eq_zero {φ : power_series k} :
  φ⁻¹ = 0 ↔ constant_coeff k φ = 0 :=
mv_power_series.inv_eq_zero

@[simp, priority 1100] lemma inv_of_unit_eq (φ : power_series k) (h : constant_coeff k φ ≠ 0) :
  inv_of_unit φ (units.mk0 _ h) = φ⁻¹ :=
mv_power_series.inv_of_unit_eq _ _

@[simp] lemma inv_of_unit_eq' (φ : power_series k) (u : units k) (h : constant_coeff k φ = u) :
  inv_of_unit φ u = φ⁻¹ :=
mv_power_series.inv_of_unit_eq' φ _ h

@[simp] protected lemma mul_inv (φ : power_series k) (h : constant_coeff k φ ≠ 0) :
  φ * φ⁻¹ = 1 :=
mv_power_series.mul_inv φ h

@[simp] protected lemma inv_mul (φ : power_series k) (h : constant_coeff k φ ≠ 0) :
  φ⁻¹ * φ = 1 :=
mv_power_series.inv_mul φ h

lemma eq_mul_inv_iff_mul_eq {φ₁ φ₂ φ₃ : power_series k} (h : constant_coeff k φ₃ ≠ 0) :
  φ₁ = φ₂ * φ₃⁻¹ ↔ φ₁ * φ₃ = φ₂ :=
mv_power_series.eq_mul_inv_iff_mul_eq h

lemma eq_inv_iff_mul_eq_one {φ ψ : power_series k} (h : constant_coeff k ψ ≠ 0) :
  φ = ψ⁻¹ ↔ φ * ψ = 1 :=
mv_power_series.eq_inv_iff_mul_eq_one h

lemma inv_eq_iff_mul_eq_one {φ ψ : power_series k} (h : constant_coeff k ψ ≠ 0) :
  ψ⁻¹ = φ ↔ φ * ψ = 1 :=
mv_power_series.inv_eq_iff_mul_eq_one h

end field

end power_series

namespace power_series
variable {R : Type*}

local attribute [instance, priority 1] classical.prop_decidable
noncomputable theory

section order_basic
open multiplicity
variables [comm_semiring R]

/-- The order of a formal power series `φ` is the greatest `n : enat`
such that `X^n` divides `φ`. The order is `⊤` if and only if `φ = 0`. -/
@[reducible] def order (φ : power_series R) : enat :=
multiplicity X φ

lemma order_finite_of_coeff_ne_zero (φ : power_series R) (h : ∃ n, coeff R n φ ≠ 0) :
  (order φ).dom :=
begin
  cases h with n h, refine ⟨n, _⟩, dsimp only,
  rw X_pow_dvd_iff, push_neg, exact ⟨n, lt_add_one n, h⟩
end

/-- If the order of a formal power series is finite,
then the coefficient indexed by the order is nonzero.-/
lemma coeff_order (φ : power_series R) (h : (order φ).dom) :
  coeff R (φ.order.get h) φ ≠ 0 :=
begin
  have H := nat.find_spec h, contrapose! H, rw X_pow_dvd_iff,
  intros m hm, by_cases Hm : m < nat.find h,
  { have := nat.find_min h Hm, push_neg at this,
    rw X_pow_dvd_iff at this, exact this m (lt_add_one m) },
  have : m = nat.find h, {linarith}, {rwa this}
end

/-- If the `n`th coefficient of a formal power series is nonzero,
then the order of the power series is less than or equal to `n`.-/
lemma order_le (φ : power_series R) (n : ℕ) (h : coeff R n φ ≠ 0) :
  order φ ≤ n :=
begin
  have h : ¬ X^(n+1) ∣ φ,
  { rw X_pow_dvd_iff, push_neg, exact ⟨n, lt_add_one n, h⟩ },
  have : (order φ).dom := ⟨n, h⟩,
  rw [← enat.coe_get this, enat.coe_le_coe],
  refine nat.find_min' this h
end

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series.-/
lemma coeff_of_lt_order (φ : power_series R) (n : ℕ) (h: ↑n < order φ) :
  coeff R n φ = 0 :=
by { contrapose! h, exact order_le _ _ h }

/-- The order of the `0` power series is infinite.-/
@[simp] lemma order_zero : order (0 : power_series R) = ⊤ :=
multiplicity.zero _

/-- The `0` power series is the unique power series with infinite order.-/
@[simp] lemma order_eq_top {φ : power_series R} :
  φ.order = ⊤ ↔ φ = 0 :=
begin
  split,
  { intro h, ext n, rw [(coeff R n).map_zero, coeff_of_lt_order], simp [h] },
  { rintros rfl, exact order_zero  }
end

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`.-/
lemma nat_le_order (φ : power_series R) (n : ℕ) (h : ∀ i < n, coeff R i φ = 0) :
  ↑n ≤ order φ :=
begin
  by_contra H, rw not_le at H,
  have : (order φ).dom := enat.dom_of_le_some (le_of_lt H),
  rw [← enat.coe_get this, enat.coe_lt_coe] at H,
  exact coeff_order _ this (h _ H)
end

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`.-/
lemma le_order (φ : power_series R) (n : enat) (h : ∀ i : ℕ, ↑i < n → coeff R i φ = 0) :
  n ≤ order φ :=
begin
  induction n using enat.cases_on,
  { show _ ≤ _, rw [top_le_iff, order_eq_top],
    ext i, exact h _ (enat.coe_lt_top i) },
  { apply nat_le_order, simpa only [enat.coe_lt_coe] using h }
end

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`.-/
lemma order_eq_nat {φ : power_series R} {n : ℕ} :
  order φ = n ↔ (coeff R n φ ≠ 0) ∧ (∀ i, i < n → coeff R i φ = 0) :=
begin
  simp only [eq_some_iff, X_pow_dvd_iff], push_neg,
  split,
  { rintros ⟨h₁, m, hm₁, hm₂⟩, refine ⟨_, h₁⟩,
    suffices : n = m, { rwa this },
    suffices : m ≥ n, { linarith },
    contrapose! hm₂, exact h₁ _ hm₂ },
  { rintros ⟨h₁, h₂⟩, exact ⟨h₂, n, lt_add_one n, h₁⟩ }
end

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`.-/
lemma order_eq {φ : power_series R} {n : enat} :
  order φ = n ↔ (∀ i:ℕ, ↑i = n → coeff R i φ ≠ 0) ∧ (∀ i:ℕ, ↑i < n → coeff R i φ = 0) :=
begin
  induction n using enat.cases_on,
  { rw order_eq_top, split,
    { rintro rfl, split; intros,
      { exfalso, exact enat.coe_ne_top ‹_› ‹_› },
      { exact (coeff _ _).map_zero } },
    { rintro ⟨h₁, h₂⟩, ext i, exact h₂ i (enat.coe_lt_top i) } },
  { simpa [enat.coe_inj] using order_eq_nat }
end

/-- The order of the sum of two formal power series
 is at least the minimum of their orders.-/
lemma le_order_add (φ ψ : power_series R) :
  min (order φ) (order ψ) ≤ order (φ + ψ) :=
multiplicity.min_le_multiplicity_add

private lemma order_add_of_order_eq.aux (φ ψ : power_series R)
  (h : order φ ≠ order ψ) (H : order φ < order ψ) :
  order (φ + ψ) ≤ order φ ⊓ order ψ :=
begin
  suffices : order (φ + ψ) = order φ,
  { rw [le_inf_iff, this], exact ⟨le_refl _, le_of_lt H⟩ },
  { rw order_eq, split,
    { intros i hi, rw [(coeff _ _).map_add, coeff_of_lt_order ψ i (hi.symm ▸ H), add_zero],
      exact (order_eq_nat.1 hi.symm).1 },
    { intros i hi,
      rw [(coeff _ _).map_add, coeff_of_lt_order φ i hi,
        coeff_of_lt_order ψ i (lt_trans hi H), zero_add] } }
end

/-- The order of the sum of two formal power series
 is the minimum of their orders if their orders differ.-/
lemma order_add_of_order_eq (φ ψ : power_series R) (h : order φ ≠ order ψ) :
  order (φ + ψ) = order φ ⊓ order ψ :=
begin
  refine le_antisymm _ (le_order_add _ _),
  by_cases H₁ : order φ < order ψ,
  { apply order_add_of_order_eq.aux _ _ h H₁ },
  by_cases H₂ : order ψ < order φ,
  { simpa only [add_comm, inf_comm] using order_add_of_order_eq.aux _ _ h.symm H₂ },
  exfalso, exact h (le_antisymm (not_lt.1 H₂) (not_lt.1 H₁))
end

/-- The order of the product of two formal power series
 is at least the sum of their orders.-/
lemma order_mul_ge (φ ψ : power_series R) :
  order φ + order ψ ≤ order (φ * ψ) :=
begin
  apply le_order,
  intros n hn, rw [coeff_mul, finset.sum_eq_zero],
  rintros ⟨i,j⟩ hij,
  by_cases hi : ↑i < order φ,
  { rw [coeff_of_lt_order φ i hi, zero_mul] },
  by_cases hj : ↑j < order ψ,
  { rw [coeff_of_lt_order ψ j hj, mul_zero] },
  rw not_lt at hi hj, rw finset.nat.mem_antidiagonal at hij,
  exfalso,
  apply ne_of_lt (lt_of_lt_of_le hn $ add_le_add hi hj),
  rw [← enat.coe_add, hij]
end

/-- The order of the monomial `a*X^n` is infinite if `a = 0` and `n` otherwise.-/
lemma order_monomial (n : ℕ) (a : R) :
  order (monomial R n a) = if a = 0 then ⊤ else n :=
begin
  split_ifs with h,
  { rw [h, order_eq_top, linear_map.map_zero] },
  { rw [order_eq], split; intros i hi,
    { rw [enat.coe_inj] at hi, rwa [hi, coeff_monomial_same] },
    { rw [enat.coe_lt_coe] at hi, rw [coeff_monomial, if_neg], exact ne_of_lt hi } }
end

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`.-/
lemma order_monomial_of_ne_zero (n : ℕ) (a : R) (h : a ≠ 0) :
  order (monomial R n a) = n :=
by rw [order_monomial, if_neg h]

end order_basic

section order_zero_ne_one
variables [comm_semiring R] [nontrivial R]

/-- The order of the formal power series `1` is `0`.-/
@[simp] lemma order_one : order (1 : power_series R) = 0 :=
by simpa using order_monomial_of_ne_zero 0 (1:R) one_ne_zero

/-- The order of the formal power series `X` is `1`.-/
@[simp] lemma order_X : order (X : power_series R) = 1 :=
order_monomial_of_ne_zero 1 (1:R) one_ne_zero

/-- The order of the formal power series `X^n` is `n`.-/
@[simp] lemma order_X_pow (n : ℕ) : order ((X : power_series R)^n) = n :=
by { rw [X_pow_eq, order_monomial_of_ne_zero], exact one_ne_zero }

end order_zero_ne_one

section order_integral_domain
variables [integral_domain R]

/-- The order of the product of two formal power series over an integral domain
 is the sum of their orders.-/
lemma order_mul (φ ψ : power_series R) :
  order (φ * ψ) = order φ + order ψ :=
multiplicity.mul (X_prime)

end order_integral_domain

end power_series

namespace polynomial
open finsupp
variables {σ : Type*} {R : Type*} [comm_semiring R]

/-- The natural inclusion from polynomials into formal power series.-/
instance coe_to_power_series : has_coe (polynomial R) (power_series R) :=
⟨λ φ, power_series.mk $ λ n, coeff φ n⟩

@[simp, norm_cast] lemma coeff_coe (φ : polynomial R) (n) :
  power_series.coeff R n φ = coeff φ n :=
congr_arg (coeff φ) (finsupp.single_eq_same)

@[simp, norm_cast] lemma coe_monomial (n : ℕ) (a : R) :
  (monomial n a : power_series R) = power_series.monomial R n a :=
power_series.ext $ λ m,
begin
  rw [coeff_coe, power_series.coeff_monomial],
  simp only [@eq_comm _ m n],
  convert finsupp.single_apply,
end

@[simp, norm_cast] lemma coe_zero : ((0 : polynomial R) : power_series R) = 0 := rfl

@[simp, norm_cast] lemma coe_one : ((1 : polynomial R) : power_series R) = 1 :=
begin
  have := coe_monomial 0 (1:R),
  rwa power_series.monomial_zero_eq_C_apply at this,
end

@[simp, norm_cast] lemma coe_add (φ ψ : polynomial R) :
  ((φ + ψ : polynomial R) : power_series R) = φ + ψ := rfl

@[simp, norm_cast] lemma coe_mul (φ ψ : polynomial R) :
  ((φ * ψ : polynomial R) : power_series R) = φ * ψ :=
power_series.ext $ λ n,
by simp only [coeff_coe, power_series.coeff_mul, coeff_mul]

@[simp, norm_cast] lemma coe_C (a : R) :
  ((C a : polynomial R) : power_series R) = power_series.C R a :=
begin
  have := coe_monomial 0 a,
  rwa power_series.monomial_zero_eq_C_apply at this,
end

@[simp, norm_cast] lemma coe_X :
  ((X : polynomial R) : power_series R) = power_series.X :=
coe_monomial _ _

/--
The coercion from polynomials to power series
as a ring homomorphism.
-/
-- TODO as an algebra homomorphism?
def coe_to_power_series.ring_hom : polynomial R →+* power_series R  :=
{ to_fun := (coe : polynomial R → power_series R),
  map_zero' := coe_zero,
  map_one' := coe_one,
  map_add' := coe_add,
  map_mul' := coe_mul }

end polynomial
