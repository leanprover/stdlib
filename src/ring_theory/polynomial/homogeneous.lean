/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.mv_polynomial

/-!
# Homogeneous polynomials

A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occuring in `φ` have degree `n`.

## Main definitions/lemmas

* `is_homogeneous φ n`: a predicate that asserts that `φ` is homogeneous of degree `n`.
* `homogeneous_component n`: the additive morphism that projects polynomials onto
  their summand that is homogeneous of degree `n`.
* `sum_homogeneous_component`: every polynomial is the sum of its homogeneous components

-/

open_locale big_operators

namespace mv_polynomial
variables {σ : Type*} {τ : Type*} {R : Type*} {S : Type*}

/-
TODO
* create definition for `∑ i in d.support, d i`
* define graded rings, and show that mv_polynomial is an example
-/

/-- A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occuring in `φ` have degree `n`. -/
def is_homogeneous [comm_semiring R] (φ : mv_polynomial σ R) (n : ℕ) :=
∀ ⦃d⦄, coeff d φ ≠ 0 → ∑ i in d.support, d i = n

section
variables [comm_semiring R]

variables {σ R}

lemma is_homogeneous_monomial (d : σ →₀ ℕ) (r : R) (n : ℕ) (hn : ∑ i in d.support, d i = n) :
  is_homogeneous (monomial d r) n :=
begin
  intros c hc,
  rw coeff_monomial at hc,
  split_ifs at hc with h,
  { subst c, exact hn },
  { contradiction }
end
variables (σ) {R}

lemma is_homogeneous_C (r : R) :
  is_homogeneous (C r : mv_polynomial σ R) 0 :=
begin
  apply is_homogeneous_monomial,
  simp only [finsupp.zero_apply, finset.sum_const_zero],
end

variables (σ R)

lemma is_homogeneous_zero (n : ℕ) : is_homogeneous (0 : mv_polynomial σ R) n :=
λ d hd, false.elim (hd $ coeff_zero _)

lemma is_homogeneous_one : is_homogeneous (1 : mv_polynomial σ R) 0 :=
is_homogeneous_C _ _

variables {σ} (R)

lemma is_homogeneous_X (i : σ) :
  is_homogeneous (X i : mv_polynomial σ R) 1 :=
begin
  apply is_homogeneous_monomial,
  simp only [finsupp.support_single_ne_zero one_ne_zero, finset.sum_singleton],
  exact finsupp.single_eq_same
end

end

namespace is_homogeneous
variables [comm_semiring R] {φ ψ : mv_polynomial σ R} {m n : ℕ}

lemma coeff_eq_zero (hφ : is_homogeneous φ n) (d : σ →₀ ℕ) (hd : ∑ i in d.support, d i ≠ n) :
  coeff d φ = 0 :=
by { have aux := mt (@hφ d) hd, classical, rwa not_not at aux }

lemma inj_right (hm : is_homogeneous φ m) (hn : is_homogeneous φ n) (hφ : φ ≠ 0) :
  m = n :=
begin
  obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero hφ,
  rw [← hm hd, ← hn hd]
end

lemma add (hφ : is_homogeneous φ n) (hψ : is_homogeneous ψ n) :
  is_homogeneous (φ + ψ) n :=
begin
  intros c hc,
  rw coeff_add at hc,
  obtain h|h : coeff c φ ≠ 0 ∨ coeff c ψ ≠ 0,
  { contrapose! hc, simp only [hc, add_zero] },
  { exact hφ h },
  { exact hψ h }
end

lemma sum {ι : Type*} (s : finset ι) (φ : ι → mv_polynomial σ R) (n : ℕ)
  (h : ∀ i ∈ s, is_homogeneous (φ i) n) :
  is_homogeneous (∑ i in s, φ i) n :=
begin
  classical,
  revert h,
  apply finset.induction_on s,
  { intro, simp only [is_homogeneous_zero, finset.sum_empty] },
  { intros i s his IH h,
    simp only [his, finset.sum_insert, not_false_iff],
    apply (h i (finset.mem_insert_self _ _)).add (IH _),
    intros j hjs,
    exact h j (finset.mem_insert_of_mem hjs) }
end

lemma mul (hφ : is_homogeneous φ m) (hψ : is_homogeneous ψ n) :
  is_homogeneous (φ * ψ) (m + n) :=
begin
  intros c hc,
  rw [coeff_mul] at hc,
  obtain ⟨⟨d, e⟩, hde, H⟩ := finset.exists_ne_zero_of_sum_ne_zero hc,
  have aux : coeff d φ ≠ 0 ∧ coeff e ψ ≠ 0,
  { contrapose! H,
    by_cases h : coeff d φ = 0;
    simp only [*, ne.def, not_false_iff, zero_mul, mul_zero] at * },
  specialize hφ aux.1, specialize hψ aux.2,
  rw finsupp.mem_antidiagonal_support at hde,
  classical,
  have hd' : d.support ⊆ d.support ∪ e.support := finset.subset_union_left _ _,
  have he' : e.support ⊆ d.support ∪ e.support := finset.subset_union_right _ _,
  rw [← hde, ← hφ, ← hψ, finset.sum_subset (finsupp.support_add),
    finset.sum_subset hd', finset.sum_subset he', ← finset.sum_add_distrib],
  { congr },
  all_goals { intros i hi, apply finsupp.not_mem_support_iff.mp }
end

lemma prod {ι : Type*} (s : finset ι) (φ : ι → mv_polynomial σ R) (n : ι → ℕ)
  (h : ∀ i ∈ s, is_homogeneous (φ i) (n i)) :
  is_homogeneous (∏ i in s, φ i) (∑ i in s, n i) :=
begin
  classical,
  revert h,
  apply finset.induction_on s,
  { intro, simp only [is_homogeneous_one, finset.sum_empty, finset.prod_empty] },
  { intros i s his IH h,
    simp only [his, finset.prod_insert, finset.sum_insert, not_false_iff],
    apply (h i (finset.mem_insert_self _ _)).mul (IH _),
    intros j hjs,
    exact h j (finset.mem_insert_of_mem hjs) }
end

lemma total_degree (hφ : is_homogeneous φ n) (h : φ ≠ 0) :
  total_degree φ = n :=
begin
  rw total_degree,
  apply le_antisymm,
  { apply finset.sup_le,
    intros d hd,
    rw finsupp.mem_support_iff at hd,
    rw [finsupp.sum, hφ hd], },
  { obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero h,
    simp only [← hφ hd, finsupp.sum],
    replace hd := finsupp.mem_support_iff.mpr hd,
    exact finset.le_sup hd, }
end

end is_homogeneous

section
noncomputable theory
open_locale classical
open finset

/-- `homogeneous_component n φ` is the part of `φ` that is homogeneous of degree `n`.
See `sum_homogeneous_component` for the statement that `φ` is equal to the sum
of all its homogeneous components. -/
def homogeneous_component [comm_semiring R] (n : ℕ) :
  mv_polynomial σ R →ₗ[R] mv_polynomial σ R :=
(submodule.subtype _).comp $ finsupp.restrict_dom _ _ {d | ∑ i in d.support, d i = n}

section homogeneous_component
open finset
variables [comm_semiring R] (n : ℕ) (φ : mv_polynomial σ R)

lemma coeff_homogeneous_component (d : σ →₀ ℕ) :
  coeff d (homogeneous_component n φ) = if ∑ i in d.support, d i = n then coeff d φ else 0 :=
by convert finsupp.filter_apply (λ d : σ →₀ ℕ, ∑ i in d.support, d i = n) φ d

lemma homogeneous_component_apply :
  homogeneous_component n φ =
  ∑ d in φ.support.filter (λ d, ∑ i in d.support, d i = n), monomial d (coeff d φ) :=
by convert finsupp.filter_eq_sum (λ d : σ →₀ ℕ, ∑ i in d.support, d i = n) φ

lemma homogeneous_component_is_homogeneous :
  (homogeneous_component n φ).is_homogeneous n :=
begin
  intros d hd,
  contrapose! hd,
  rw [coeff_homogeneous_component, if_neg hd]
end

lemma homogeneous_component_zero : homogeneous_component 0 φ = C (coeff 0 φ) :=
begin
  ext1 d,
  rcases em (d = 0) with (rfl|hd),
  { simp only [coeff_homogeneous_component, sum_eq_zero_iff, finsupp.coe_zero, if_true, coeff_C,
      eq_self_iff_true, forall_true_iff] },
  { rw [coeff_homogeneous_component, if_neg, coeff_C, if_neg (ne.symm hd)],
    simp only [finsupp.ext_iff, finsupp.zero_apply] at hd,
    simp [hd] }
end

lemma homogeneous_component_eq_zero' (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → ∑ i in d.support, d i ≠ n) :
  homogeneous_component n φ = 0 :=
begin
  rw [homogeneous_component_apply, sum_eq_zero],
  intros d hd, rw mem_filter at hd,
  exfalso, exact h _ hd.1 hd.2
end

lemma homogeneous_component_eq_zero (h : φ.total_degree < n) :
  homogeneous_component n φ = 0 :=
begin
  apply homogeneous_component_eq_zero',
  rw [total_degree, finset.sup_lt_iff] at h,
  { intros d hd, exact ne_of_lt (h d hd), },
  { exact lt_of_le_of_lt (nat.zero_le _) h, }
end

lemma sum_homogeneous_component :
  ∑ i in range (φ.total_degree + 1), homogeneous_component i φ = φ :=
begin
  ext1 d,
  suffices : φ.total_degree < d.support.sum d → 0 = coeff d φ,
    by simpa [coeff_sum, coeff_homogeneous_component],
  exact λ h, (coeff_eq_zero_of_total_degree_lt h).symm
end

end homogeneous_component

end

end mv_polynomial
