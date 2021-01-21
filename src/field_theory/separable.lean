/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau.
-/

import algebra.polynomial.big_operators
import field_theory.splitting_field
import field_theory.tower
import algebra.squarefree

/-!

# Separable polynomials

We define a polynomial to be separable if it is coprime with its derivative. We prove basic
properties about separable polynomials here.

## Main definitions

* `polynomial.separable f`: a polynomial `f` is separable iff it is coprime with its derivative.
* `polynomial.expand R p f`: expand the polynomial `f` with coefficients in a
  commutative semiring `R` by a factor of p, so `expand R p (∑ aₙ xⁿ)` is `∑ aₙ xⁿᵖ`.
* `polynomial.contract p f`: the opposite of `expand`, so it sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`.

-/

universes u v w
open_locale classical big_operators
open finset

namespace polynomial

section comm_semiring

variables {R : Type u} [comm_semiring R] {S : Type v} [comm_semiring S]

/-- A polynomial is separable iff it is coprime with its derivative. -/
def separable (f : polynomial R) : Prop :=
is_coprime f f.derivative

lemma separable_def (f : polynomial R) :
  f.separable ↔ is_coprime f f.derivative :=
iff.rfl

lemma separable_def' (f : polynomial R) :
  f.separable ↔ ∃ a b : polynomial R, a * f + b * f.derivative = 1 :=
iff.rfl

lemma separable_one : (1 : polynomial R).separable :=
is_coprime_one_left

lemma separable_X_add_C (a : R) : (X + C a).separable :=
by { rw [separable_def, derivative_add, derivative_X, derivative_C, add_zero],
  exact is_coprime_one_right }

lemma separable_X : (X : polynomial R).separable :=
by { rw [separable_def, derivative_X], exact is_coprime_one_right }

lemma separable_C (r : R) : (C r).separable ↔ is_unit r :=
by rw [separable_def, derivative_C, is_coprime_zero_right, is_unit_C]

lemma separable.of_mul_left {f g : polynomial R} (h : (f * g).separable) : f.separable :=
begin
  have := h.of_mul_left_left, rw derivative_mul at this,
  exact is_coprime.of_mul_right_left (is_coprime.of_add_mul_left_right this)
end

lemma separable.of_mul_right {f g : polynomial R} (h : (f * g).separable) : g.separable :=
by { rw mul_comm at h, exact h.of_mul_left }

lemma separable.of_dvd {f g : polynomial R} (hf : f.separable) (hfg : g ∣ f) : g.separable :=
by { rcases hfg with ⟨f', rfl⟩, exact separable.of_mul_left hf }

lemma separable_gcd_left {F : Type*} [field F] {f : polynomial F}
  (hf : f.separable) (g : polynomial F) : (euclidean_domain.gcd f g).separable :=
separable.of_dvd hf (euclidean_domain.gcd_dvd_left f g)

lemma separable_gcd_right {F : Type*} [field F] {g : polynomial F}
  (f : polynomial F) (hg : g.separable) : (euclidean_domain.gcd f g).separable :=
separable.of_dvd hg (euclidean_domain.gcd_dvd_right f g)

lemma separable.is_coprime {f g : polynomial R} (h : (f * g).separable) : is_coprime f g :=
begin
  have := h.of_mul_left_left, rw derivative_mul at this,
  exact is_coprime.of_mul_right_right (is_coprime.of_add_mul_left_right this)
end

theorem separable.of_pow' {f : polynomial R} :
  ∀ {n : ℕ} (h : (f ^ n).separable), is_unit f ∨ (f.separable ∧ n = 1) ∨ n = 0
| 0     := λ h, or.inr $ or.inr rfl
| 1     := λ h, or.inr $ or.inl ⟨pow_one f ▸ h, rfl⟩
| (n+2) := λ h, or.inl $ is_coprime_self.1 h.is_coprime.of_mul_right_left

theorem separable.of_pow {f : polynomial R} (hf : ¬is_unit f) {n : ℕ} (hn : n ≠ 0)
  (hfs : (f ^ n).separable) : f.separable ∧ n = 1 :=
(hfs.of_pow'.resolve_left hf).resolve_right hn

theorem separable.map {p : polynomial R} (h : p.separable) {f : R →+* S} : (p.map f).separable :=
let ⟨a, b, H⟩ := h in ⟨a.map f, b.map f,
by rw [derivative_map, ← map_mul, ← map_mul, ← map_add, H, map_one]⟩

variables (R) (p q : ℕ)

/-- Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`. -/
noncomputable def expand : polynomial R →ₐ[R] polynomial R :=
{ commutes' := λ r, eval₂_C _ _,
  .. (eval₂_ring_hom C (X ^ p) : polynomial R →+* polynomial R) }

lemma coe_expand : (expand R p : polynomial R → polynomial R) = eval₂ C (X ^ p) := rfl

variables {R}

lemma expand_eq_sum {f : polynomial R} :
  expand R p f = f.sum (λ e a, C a * (X ^ p) ^ e) :=
by { dsimp [expand, eval₂], refl, }

@[simp] lemma expand_C (r : R) : expand R p (C r) = C r := eval₂_C _ _
@[simp] lemma expand_X : expand R p X = X ^ p := eval₂_X _ _
@[simp] lemma expand_monomial (r : R) : expand R p (monomial q r) = monomial (q * p) r :=
by simp_rw [monomial_eq_smul_X, alg_hom.map_smul, alg_hom.map_pow, expand_X, mul_comm, pow_mul]

theorem expand_expand (f : polynomial R) : expand R p (expand R q f) = expand R (p * q) f :=
polynomial.induction_on f (λ r, by simp_rw expand_C)
  (λ f g ihf ihg, by simp_rw [alg_hom.map_add, ihf, ihg])
  (λ n r ih, by simp_rw [alg_hom.map_mul, expand_C, alg_hom.map_pow, expand_X,
    alg_hom.map_pow, expand_X, pow_mul])

theorem expand_mul (f : polynomial R) : expand R (p * q) f = expand R p (expand R q f) :=
(expand_expand p q f).symm

@[simp] theorem expand_one (f : polynomial R) : expand R 1 f = f :=
polynomial.induction_on f
  (λ r, by rw expand_C)
  (λ f g ihf ihg, by rw [alg_hom.map_add, ihf, ihg])
  (λ n r ih, by rw [alg_hom.map_mul, expand_C, alg_hom.map_pow, expand_X, pow_one])

theorem expand_pow (f : polynomial R) : expand R (p ^ q) f = (expand R p ^[q] f) :=
nat.rec_on q (by rw [pow_zero, expand_one, function.iterate_zero, id]) $ λ n ih,
by rw [function.iterate_succ_apply', pow_succ, expand_mul, ih]

theorem derivative_expand (f : polynomial R) :
  (expand R p f).derivative = expand R p f.derivative * (p * X ^ (p - 1)) :=
by rw [coe_expand, derivative_eval₂_C, derivative_pow, derivative_X, mul_one]

theorem coeff_expand {p : ℕ} (hp : 0 < p) (f : polynomial R) (n : ℕ) :
  (expand R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0 :=
begin
  simp only [expand_eq_sum],
  simp_rw [coeff_sum, ← pow_mul, C_mul_X_pow_eq_monomial, coeff_monomial, finsupp.sum],
  split_ifs with h,
  { rw [finset.sum_eq_single (n/p), nat.mul_div_cancel' h, if_pos rfl], refl,
    { intros b hb1 hb2, rw if_neg, intro hb3, apply hb2, rw [← hb3, nat.mul_div_cancel_left b hp] },
    { intro hn, rw finsupp.not_mem_support_iff.1 hn, split_ifs; refl } },
  { rw finset.sum_eq_zero, intros k hk, rw if_neg, exact λ hkn, h ⟨k, hkn.symm⟩, },
end

@[simp] theorem coeff_expand_mul {p : ℕ} (hp : 0 < p) (f : polynomial R) (n : ℕ) :
  (expand R p f).coeff (n * p) = f.coeff n :=
by rw [coeff_expand hp, if_pos (dvd_mul_left _ _), nat.mul_div_cancel _ hp]

@[simp] theorem coeff_expand_mul' {p : ℕ} (hp : 0 < p) (f : polynomial R) (n : ℕ) :
  (expand R p f).coeff (p * n) = f.coeff n :=
by rw [mul_comm, coeff_expand_mul hp]

theorem expand_eq_map_domain (p : ℕ) (f : polynomial R) :
  expand R p f = f.map_domain (*p) :=
polynomial.induction_on' f (λ p q hp hq, by simp [*, finsupp.map_domain_add]) $
  λ n a, by simp_rw [expand_monomial, monomial_def, finsupp.map_domain_single]

theorem expand_inj {p : ℕ} (hp : 0 < p) {f g : polynomial R} :
  expand R p f = expand R p g ↔ f = g :=
⟨λ H, ext $ λ n, by rw [← coeff_expand_mul hp, H, coeff_expand_mul hp], congr_arg _⟩

theorem expand_eq_zero {p : ℕ} (hp : 0 < p) {f : polynomial R} : expand R p f = 0 ↔ f = 0 :=
by rw [← (expand R p).map_zero, expand_inj hp, alg_hom.map_zero]

theorem expand_eq_C {p : ℕ} (hp : 0 < p) {f : polynomial R} {r : R} :
  expand R p f = C r ↔ f = C r :=
by rw [← expand_C, expand_inj hp, expand_C]

theorem nat_degree_expand (p : ℕ) (f : polynomial R) :
  (expand R p f).nat_degree = f.nat_degree * p :=
begin
  cases p.eq_zero_or_pos with hp hp,
  { rw [hp, coe_expand, pow_zero, mul_zero, ← C_1, eval₂_hom, nat_degree_C] },
  by_cases hf : f = 0,
  { rw [hf, alg_hom.map_zero, nat_degree_zero, zero_mul] },
  have hf1 : expand R p f ≠ 0 := mt (expand_eq_zero hp).1 hf,
  rw [← with_bot.coe_eq_coe, ← degree_eq_nat_degree hf1],
  refine le_antisymm ((degree_le_iff_coeff_zero _ _).2 $ λ n hn, _) _,
  { rw coeff_expand hp, split_ifs with hpn,
    { rw coeff_eq_zero_of_nat_degree_lt, contrapose! hn,
      rw [with_bot.coe_le_coe, ← nat.div_mul_cancel hpn], exact nat.mul_le_mul_right p hn },
    { refl } },
  { refine le_degree_of_ne_zero _,
    rw [coeff_expand_mul hp, ← leading_coeff], exact mt leading_coeff_eq_zero.1 hf }
end

theorem map_expand {p : ℕ} (hp : 0 < p) {f : R →+* S} {q : polynomial R} :
  map f (expand R p q) = expand S p (map f q) :=
by { ext, rw [coeff_map, coeff_expand hp, coeff_expand hp], split_ifs; simp, }

end comm_semiring

section comm_ring

variables {R : Type u} [comm_ring R]

lemma separable_X_sub_C {x : R} : separable (X - C x) :=
by simpa only [sub_eq_add_neg, C_neg] using separable_X_add_C (-x)

lemma separable.mul {f g : polynomial R} (hf : f.separable) (hg : g.separable)
  (h : is_coprime f g) : (f * g).separable :=
by { rw [separable_def, derivative_mul], exact ((hf.mul_right h).add_mul_left_right _).mul_left
  ((h.symm.mul_right hg).mul_add_right_right _) }

lemma separable_prod' {ι : Sort*} {f : ι → polynomial R} {s : finset ι} :
  (∀x∈s, ∀y∈s, x ≠ y → is_coprime (f x) (f y)) → (∀x∈s, (f x).separable) →
  (∏ x in s, f x).separable :=
finset.induction_on s (λ _ _, separable_one) $ λ a s has ih h1 h2, begin
  simp_rw [finset.forall_mem_insert, forall_and_distrib] at h1 h2, rw prod_insert has,
  exact h2.1.mul (ih h1.2.2 h2.2) (is_coprime.prod_right $ λ i his, h1.1.2 i his $
    ne.symm $ ne_of_mem_of_not_mem his has)
end

lemma separable_prod {ι : Sort*} [fintype ι] {f : ι → polynomial R}
  (h1 : pairwise (is_coprime on f)) (h2 : ∀ x, (f x).separable) : (∏ x, f x).separable :=
separable_prod' (λ x hx y hy hxy, h1 x y hxy) (λ x hx, h2 x)

lemma separable.inj_of_prod_X_sub_C [nontrivial R] {ι : Sort*} {f : ι → R} {s : finset ι}
  (hfs : (∏ i in s, (X - C (f i))).separable)
  {x y : ι} (hx : x ∈ s) (hy : y ∈ s) (hfxy : f x = f y) : x = y :=
begin
  by_contra hxy,
  rw [← insert_erase hx, prod_insert (not_mem_erase _ _),
      ← insert_erase (mem_erase_of_ne_of_mem (ne.symm hxy) hy),
      prod_insert (not_mem_erase _ _), ← mul_assoc, hfxy, ← pow_two] at hfs,
  cases (hfs.of_mul_left.of_pow (by exact not_is_unit_X_sub_C) two_ne_zero).2
end

lemma separable.injective_of_prod_X_sub_C [nontrivial R] {ι : Sort*} [fintype ι] {f : ι → R}
  (hfs : (∏ i, (X - C (f i))).separable) : function.injective f :=
λ x y hfxy, hfs.inj_of_prod_X_sub_C (mem_univ _) (mem_univ _) hfxy

lemma is_unit_of_self_mul_dvd_separable {p q : polynomial R}
  (hp : p.separable) (hq : q * q ∣ p) : is_unit q :=
begin
  obtain ⟨p, rfl⟩ := hq,
  apply is_coprime_self.mp,
  have : is_coprime (q * (q * p)) (q * (q.derivative * p + q.derivative * p + q * p.derivative)),
  { simp only [← mul_assoc, mul_add],
    convert hp,
    rw [derivative_mul, derivative_mul],
    ring },
  exact is_coprime.of_mul_right_left (is_coprime.of_mul_left_left this)
end

end comm_ring

section integral_domain

variables (R : Type u) [integral_domain R]

theorem is_local_ring_hom_expand {p : ℕ} (hp : 0 < p) :
  is_local_ring_hom (↑(expand R p) : polynomial R →+* polynomial R) :=
begin
  refine ⟨λ f hf1, _⟩, rw ← coe_fn_coe_base at hf1,
  have hf2 := eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit hf1),
  rw [coeff_expand hp, if_pos (dvd_zero _), p.zero_div] at hf2,
  rw [hf2, is_unit_C] at hf1, rw expand_eq_C hp at hf2, rwa [hf2, is_unit_C]
end

end integral_domain

section field

variables {F : Type u} [field F] {K : Type v} [field K]

theorem separable_iff_derivative_ne_zero {f : polynomial F} (hf : irreducible f) :
  f.separable ↔ f.derivative ≠ 0 :=
⟨λ h1 h2, hf.1 $ is_coprime_zero_right.1 $ h2 ▸ h1,
λ h, is_coprime_of_dvd (mt and.right h) $ λ g hg1 hg2 ⟨p, hg3⟩ hg4,
let ⟨u, hu⟩ := (hf.2 _ _ hg3).resolve_left hg1 in
have f ∣ f.derivative, by { conv_lhs { rw [hg3, ← hu] }, rwa units.mul_right_dvd },
not_lt_of_le (nat_degree_le_of_dvd this h) $ nat_degree_derivative_lt h⟩

theorem separable_map (f : F →+* K) {p : polynomial F} : (p.map f).separable ↔ p.separable :=
by simp_rw [separable_def, derivative_map, is_coprime_map]

section char_p

variables (p : ℕ) [hp : fact p.prime]
include hp

/-- The opposite of `expand`: sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`. -/
noncomputable def contract (f : polynomial F) : polynomial F :=
⟨f.support.preimage (*p) $ λ _ _ _ _, (nat.mul_left_inj hp.pos).1,
λ n, f.coeff (n * p),
λ n, by { rw [finset.mem_preimage, finsupp.mem_support_iff], refl }⟩

theorem coeff_contract (f : polynomial F) (n : ℕ) : (contract p f).coeff n = f.coeff (n * p) := rfl

theorem of_irreducible_expand {f : polynomial F} (hf : irreducible (expand F p f)) :
  irreducible f :=
@@of_irreducible_map _ _ _ (is_local_ring_hom_expand F hp.pos) hf

theorem of_irreducible_expand_pow {f : polynomial F} {n : ℕ} :
  irreducible (expand F (p ^ n) f) → irreducible f :=
nat.rec_on n (λ hf, by rwa [pow_zero, expand_one] at hf) $ λ n ih hf,
ih $ of_irreducible_expand p $ by rwa [expand_expand]

variables [HF : char_p F p]
include HF

theorem expand_char (f : polynomial F) :
  map (frobenius F p) (expand F p f) = f ^ p :=
begin
  refine f.induction_on' (λ a b ha hb, _) (λ n a, _),
  { rw [alg_hom.map_add, map_add, ha, hb, add_pow_char], },
  { rw [expand_monomial, map_monomial, single_eq_C_mul_X, single_eq_C_mul_X,
        mul_pow, ← C.map_pow, frobenius_def],
    ring_exp }
end

theorem map_expand_pow_char (f : polynomial F) (n : ℕ) :
   map ((frobenius F p) ^ n) (expand F (p ^ n) f) = f ^ (p ^ n) :=
begin
  induction n, {simp [ring_hom.one_def]},
  symmetry,
  rw [pow_succ', pow_mul, ← n_ih, ← expand_char, pow_succ, ring_hom.mul_def, ← map_map, mul_comm,
      expand_mul, ← map_expand (nat.prime.pos hp)],
end

theorem expand_contract {f : polynomial F} (hf : f.derivative = 0) :
  expand F p (contract p f) = f :=
begin
  ext n, rw [coeff_expand hp.pos, coeff_contract], split_ifs with h,
  { rw nat.div_mul_cancel h },
  { cases n, { exact absurd (dvd_zero p) h },
    have := coeff_derivative f n, rw [hf, coeff_zero, zero_eq_mul] at this, cases this, { rw this },
    rw [← nat.cast_succ, char_p.cast_eq_zero_iff F p] at this,
    exact absurd this h }
end

theorem separable_or {f : polynomial F} (hf : irreducible f) : f.separable ∨
  ¬f.separable ∧ ∃ g : polynomial F, irreducible g ∧ expand F p g = f :=
if H : f.derivative = 0 then or.inr
  ⟨by rw [separable_iff_derivative_ne_zero hf, not_not, H],
  contract p f,
  by haveI := is_local_ring_hom_expand F hp.pos; exact
    of_irreducible_map ↑(expand F p) (by rwa ← expand_contract p H at hf),
  expand_contract p H⟩
else or.inl $ (separable_iff_derivative_ne_zero hf).2 H

theorem exists_separable_of_irreducible {f : polynomial F} (hf : irreducible f) (hf0 : f ≠ 0) :
  ∃ (n : ℕ) (g : polynomial F), g.separable ∧ expand F (p ^ n) g = f :=
begin
  generalize hn : f.nat_degree = N, unfreezingI { revert f },
  apply nat.strong_induction_on N, intros N ih f hf hf0 hn,
  rcases separable_or p hf with h | ⟨h1, g, hg, hgf⟩,
  { refine ⟨0, f, h, _⟩, rw [pow_zero, expand_one] },
  { cases N with N,
    { rw [nat_degree_eq_zero_iff_degree_le_zero, degree_le_zero_iff] at hn,
      rw [hn, separable_C, is_unit_iff_ne_zero, not_not] at h1,
      rw [h1, C_0] at hn, exact absurd hn hf0 },
    have hg1 : g.nat_degree * p = N.succ,
    { rwa [← nat_degree_expand, hgf] },
    have hg2 : g.nat_degree ≠ 0,
    { intro this, rw [this, zero_mul] at hg1, cases hg1 },
    have hg3 : g.nat_degree < N.succ,
    { rw [← mul_one g.nat_degree, ← hg1],
      exact nat.mul_lt_mul_of_pos_left hp.one_lt (nat.pos_of_ne_zero hg2) },
    have hg4 : g ≠ 0,
    { rintro rfl, exact hg2 nat_degree_zero },
    rcases ih _ hg3 hg hg4 rfl with ⟨n, g, hg5, rfl⟩, refine ⟨n+1, g, hg5, _⟩,
    rw [← hgf, expand_expand, pow_succ] }
end

theorem is_unit_or_eq_zero_of_separable_expand {f : polynomial F} (n : ℕ)
  (hf : (expand F (p ^ n) f).separable) : is_unit f ∨ n = 0 :=
begin
  rw or_iff_not_imp_right, intro hn,
  have hf2 : (expand F (p ^ n) f).derivative = 0,
  { by rw [derivative_expand, nat.cast_pow, char_p.cast_eq_zero,
      zero_pow (nat.pos_of_ne_zero hn), zero_mul, mul_zero] },
  rw [separable_def, hf2, is_coprime_zero_right, is_unit_iff] at hf, rcases hf with ⟨r, hr, hrf⟩,
  rw [eq_comm, expand_eq_C (pow_pos hp.pos _)] at hrf,
  rwa [hrf, is_unit_C]
end

theorem unique_separable_of_irreducible {f : polynomial F} (hf : irreducible f) (hf0 : f ≠ 0)
  (n₁ : ℕ) (g₁ : polynomial F) (hg₁ : g₁.separable) (hgf₁ : expand F (p ^ n₁) g₁ = f)
  (n₂ : ℕ) (g₂ : polynomial F) (hg₂ : g₂.separable) (hgf₂ : expand F (p ^ n₂) g₂ = f) :
  n₁ = n₂ ∧ g₁ = g₂ :=
begin
  revert g₁ g₂, wlog hn : n₁ ≤ n₂ := le_total n₁ n₂ using [n₁ n₂, n₂ n₁] tactic.skip,
  unfreezingI { intros, rw le_iff_exists_add at hn, rcases hn with ⟨k, rfl⟩,
    rw [← hgf₁, pow_add, expand_mul, expand_inj (pow_pos hp.pos n₁)] at hgf₂, subst hgf₂,
    subst hgf₁,
    rcases is_unit_or_eq_zero_of_separable_expand p k hg₁ with h | rfl,
    { rw is_unit_iff at h, rcases h with ⟨r, hr, rfl⟩,
      simp_rw expand_C at hf, exact absurd (is_unit_C.2 hr) hf.1 },
    { rw [add_zero, pow_zero, expand_one], split; refl } },
  exact λ g₁ g₂ hg₁ hgf₁ hg₂ hgf₂, let ⟨hn, hg⟩ :=
    this g₂ g₁ hg₂ hgf₂ hg₁ hgf₁ in ⟨hn.symm, hg.symm⟩
end

end char_p

lemma separable_prod_X_sub_C_iff' {ι : Sort*} {f : ι → F} {s : finset ι} :
  (∏ i in s, (X - C (f i))).separable ↔ (∀ (x ∈ s) (y ∈ s), f x = f y → x = y) :=
⟨λ hfs x hx y hy hfxy, hfs.inj_of_prod_X_sub_C hx hy hfxy,
λ H, by { rw ← prod_attach, exact separable_prod' (λ x hx y hy hxy,
    @pairwise_coprime_X_sub _ _ { x // x ∈ s } (λ x, f x)
      (λ x y hxy, subtype.eq $ H x.1 x.2 y.1 y.2 hxy) _ _ hxy)
  (λ _ _, separable_X_sub_C) }⟩

lemma separable_prod_X_sub_C_iff {ι : Sort*} [fintype ι] {f : ι → F} :
  (∏ i, (X - C (f i))).separable ↔ function.injective f :=
separable_prod_X_sub_C_iff'.trans $ by simp_rw [mem_univ, true_implies_iff]

section splits

open_locale big_operators

variables {i : F →+* K}

lemma not_unit_X_sub_C (a : F) : ¬ is_unit (X - C a) :=
λ h, have one_eq_zero : (1 : with_bot ℕ) = 0, by simpa using degree_eq_zero_of_is_unit h,
one_ne_zero (option.some_injective _ one_eq_zero)

lemma nodup_of_separable_prod {s : multiset F}
  (hs : separable (multiset.map (λ a, X - C a) s).prod) : s.nodup :=
begin
  rw multiset.nodup_iff_ne_cons_cons,
  rintros a t rfl,
  refine not_unit_X_sub_C a (is_unit_of_self_mul_dvd_separable hs _),
  simpa only [multiset.map_cons, multiset.prod_cons] using mul_dvd_mul_left _ (dvd_mul_right _ _)
end

lemma multiplicity_le_one_of_separable {p q : polynomial F} (hq : ¬ is_unit q)
  (hsep : separable p) : multiplicity q p ≤ 1 :=
begin
  contrapose! hq,
  apply is_unit_of_self_mul_dvd_separable hsep,
  rw ← pow_two,
  apply multiplicity.pow_dvd_of_le_multiplicity,
  exact_mod_cast (enat.add_one_le_of_lt hq)
end

lemma separable.squarefree {p : polynomial F}  (hsep : separable p) : squarefree p :=
begin
  rw multiplicity.squarefree_iff_multiplicity_le_one p,
  intro f,
  by_cases hunit : is_unit f,
  { exact or.inr hunit },
  exact or.inl (multiplicity_le_one_of_separable hunit hsep)
end

/--If `n ≠ 0` in `F`, then ` X ^ n - a` is separable for any `a ≠ 0`. -/
lemma separable_X_pow_sub_C {n : ℕ} (a : F) (hn : (n : F) ≠ 0) (ha : a ≠ 0) :
  separable (X ^ n - C a) :=
begin
  cases nat.eq_zero_or_pos n with hzero hpos,
  { exfalso,
    rw hzero at hn,
    exact hn (refl 0) },
  apply (separable_def' (X ^ n - C a)).2,
  use [-C (a⁻¹), (C ((a⁻¹) * (↑n)⁻¹) *  X)],
  have mul_pow_sub : X * X ^ (n - 1) = X ^ n,
  { nth_rewrite 0 [←pow_one X],
    rw pow_mul_pow_sub X (nat.succ_le_iff.mpr hpos) },
  rw [derivative_sub, derivative_C, sub_zero, derivative_pow X n, derivative_X, mul_one],
  have hcalc : C (a⁻¹ * (↑n)⁻¹) * (↑n * (X ^ n)) = C a⁻¹ * (X ^ n),
  { calc C (a⁻¹ * (↑n)⁻¹) * (↑n * (X ^ n))
       = C a⁻¹ * C ((↑n)⁻¹) * (C ↑n * (X ^ n)) : by rw [C_mul, C_eq_nat_cast]
   ... = C a⁻¹ * (C ((↑n)⁻¹) * C ↑n) * (X ^ n) : by ring
   ... = C a⁻¹ * C ((↑n)⁻¹ * ↑n) * (X ^ n) : by rw [← C_mul]
   ... = C a⁻¹ * C 1 * (X ^ n) : by field_simp [hn]
   ... = C a⁻¹ * (X ^ n) : by rw [C_1, mul_one] },
  calc -C a⁻¹ * (X ^ n - C a) + C (a⁻¹ * (↑n)⁻¹) * X * (↑n * X ^ (n - 1))
      = -C a⁻¹ * (X ^ n - C a) + C (a⁻¹ * (↑n)⁻¹) * (↑n * (X * X ^ (n - 1))) : by ring
  ... = -C a⁻¹ * (X ^ n - C a) + C a⁻¹ * (X ^ n) : by rw [mul_pow_sub, hcalc]
  ... = C a⁻¹ * C a : by ring
  ... = (1 : polynomial F) : by rw [← C_mul, inv_mul_cancel ha, C_1]
end

/--If `n ≠ 0` in `F`, then ` X ^ n - a` is squarefree for any `a ≠ 0`. -/
lemma squarefree_X_pow_sub_C {n : ℕ} (a : F) (hn : (n : F) ≠ 0) (ha : a ≠ 0) :
  squarefree (X ^ n - C a) :=
(separable_X_pow_sub_C a hn ha).squarefree

lemma root_multiplicity_le_one_of_separable {p : polynomial F} (hp : p ≠ 0)
  (hsep : separable p) (x : F) : root_multiplicity x p ≤ 1 :=
begin
  rw [root_multiplicity_eq_multiplicity, dif_neg hp, ← enat.coe_le_coe, enat.coe_get],
  exact multiplicity_le_one_of_separable (not_unit_X_sub_C _) hsep
end

lemma count_roots_le_one {p : polynomial F} (hsep : separable p) (x : F) :
  p.roots.count x ≤ 1 :=
begin
  by_cases hp : p = 0,
  { simp [hp] },
  rw count_roots hp,
  exact root_multiplicity_le_one_of_separable hp hsep x
end

lemma nodup_roots {p : polynomial F} (hsep : separable p) :
  p.roots.nodup :=
multiset.nodup_iff_count_le_one.mpr (count_roots_le_one hsep)

lemma eq_X_sub_C_of_separable_of_root_eq {x : F} {h : polynomial F} (h_ne_zero : h ≠ 0)
  (h_sep : h.separable) (h_root : h.eval x = 0) (h_splits : splits i h)
  (h_roots : ∀ y ∈ (h.map i).roots, y = i x) : h = (C (leading_coeff h)) * (X - C x) :=
begin
  apply polynomial.eq_X_sub_C_of_splits_of_single_root i h_splits,
  apply finset.mk.inj,
  { change _ = {i x},
    rw finset.eq_singleton_iff_unique_mem,
    split,
    { apply finset.mem_mk.mpr,
      rw mem_roots (show h.map i ≠ 0, by exact map_ne_zero h_ne_zero),
      rw [is_root.def,←eval₂_eq_eval_map,eval₂_hom,h_root],
      exact ring_hom.map_zero i },
    { exact h_roots } },
  { exact nodup_roots (separable.map h_sep) },
end

end splits

end field

end polynomial

open polynomial

theorem irreducible.separable {F : Type u} [field F] [char_zero F] {f : polynomial F}
  (hf : irreducible f) : f.separable :=
begin
  rw [separable_iff_derivative_ne_zero hf, ne, ← degree_eq_bot, degree_derivative_eq], rintro ⟨⟩,
  rw [pos_iff_ne_zero, ne, nat_degree_eq_zero_iff_degree_le_zero, degree_le_zero_iff],
  refine λ hf1, hf.1 _, rw [hf1, is_unit_C, is_unit_iff_ne_zero],
  intro hf2, rw [hf2, C_0] at hf1, exact absurd hf1 hf.ne_zero
end

-- TODO: refactor to allow transcendental extensions?
-- See: https://en.wikipedia.org/wiki/Separable_extension#Separability_of_transcendental_extensions

/-- Typeclass for separable field extension: `K` is a separable field extension of `F` iff
the minimal polynomial of every `x : K` is separable. -/
@[class] def is_separable (F K : Sort*) [field F] [field K] [algebra F K] : Prop :=
∀ x : K, is_integral F x ∧ (minpoly F x).separable

instance is_separable_self (F : Type*) [field F] : is_separable F F :=
λ x, ⟨is_integral_algebra_map, by { rw minpoly.eq_X_sub_C', exact separable_X_sub_C }⟩

section is_separable_tower
variables (F K E : Type*) [field F] [field K] [field E] [algebra F K] [algebra F E]
  [algebra K E] [is_scalar_tower F K E]

lemma is_separable_tower_top_of_is_separable [h : is_separable F E] : is_separable K E :=
λ x, (h x).imp (is_integral_of_is_scalar_tower x) $
  λ hx, hx.map.of_dvd (minpoly.dvd_map_of_is_scalar_tower _ _ _)

lemma is_separable_tower_bot_of_is_separable [h : is_separable F E] : is_separable F K :=
begin
  intro x,
  refine (h (algebra_map K E x)).imp is_integral_tower_bot_of_is_integral_field _,
  intro hs,
  obtain ⟨q, hq⟩ := minpoly.dvd F x
    (is_scalar_tower.aeval_eq_zero_of_aeval_algebra_map_eq_zero_field
      (minpoly.aeval F ((algebra_map K E) x))),
  rw hq at hs,
  exact hs.of_mul_left
end

variables {E}

lemma is_separable.of_alg_hom (E' : Type*) [field E'] [algebra F E']
  (f : E →ₐ[F] E') [is_separable F E'] : is_separable F E :=
begin
  letI : algebra E E' := ring_hom.to_algebra f.to_ring_hom,
  haveI : is_scalar_tower F E E' := is_scalar_tower.of_algebra_map_eq (λ x, (f.commutes x).symm),
  exact is_separable_tower_bot_of_is_separable F E E',
end

end is_separable_tower
