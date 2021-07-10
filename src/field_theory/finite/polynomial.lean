/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import field_theory.finite.basic
import field_theory.mv_polynomial
import data.mv_polynomial.expand
import linear_algebra.basic
import linear_algebra.finite_dimensional

/-!
## Polynomials over finite fields
-/

namespace mv_polynomial
variables {σ : Type*}

/-- A polynomial over the integers is divisible by `n : ℕ`
if and only if it is zero over `zmod n`. -/
lemma C_dvd_iff_zmod (n : ℕ) (φ : mv_polynomial σ ℤ) :
  C (n:ℤ) ∣ φ ↔ map (int.cast_ring_hom (zmod n)) φ = 0 :=
C_dvd_iff_map_hom_eq_zero _ _ (char_p.int_cast_eq_zero_iff (zmod n) n) _

section frobenius

variables {p : ℕ} [fact p.prime]

lemma frobenius_zmod (f : mv_polynomial σ (zmod p)) :
  frobenius _ p f = expand p f :=
begin
  apply induction_on f,
  { intro a, rw [expand_C, frobenius_def, ← C_pow, zmod.pow_card], },
  { simp only [alg_hom.map_add, ring_hom.map_add], intros _ _ hf hg, rw [hf, hg] },
  { simp only [expand_X, ring_hom.map_mul, alg_hom.map_mul],
    intros _ _ hf, rw [hf, frobenius_def], },
end

lemma expand_zmod (f : mv_polynomial σ (zmod p)) :
  expand p f = f ^ p :=
(frobenius_zmod _).symm

end frobenius

end mv_polynomial

namespace mv_polynomial

noncomputable theory
open_locale big_operators classical
open set linear_map submodule

variables {K : Type*} {σ : Type*}
variables [field K] [fintype K] [fintype σ]

def indicator (a : σ → K) : mv_polynomial σ K :=
∏ n, (1 - (X n - C (a n))^(fintype.card K - 1))

lemma eval_indicator_apply_eq_one (a : σ → K) :
  eval a (indicator a) = 1 :=
have 0 < fintype.card K - 1,
begin
  rw [← finite_field.card_units, fintype.card_pos_iff],
  exact ⟨1⟩
end,
by simp only [indicator, (finset.univ.prod_hom (eval a)).symm, ring_hom.map_sub,
    is_ring_hom.map_one (eval a), is_monoid_hom.map_pow (eval a), eval_X, eval_C,
    sub_self, zero_pow this, sub_zero, finset.prod_const_one]

lemma eval_indicator_apply_eq_zero (a b : σ → K) (h : a ≠ b) :
  eval a (indicator b) = 0 :=
have ∃i, a i ≠ b i, by rwa [(≠), function.funext_iff, not_forall] at h,
begin
  rcases this with ⟨i, hi⟩,
  simp only [indicator, (finset.univ.prod_hom (eval a)).symm, ring_hom.map_sub,
    is_ring_hom.map_one (eval a), is_monoid_hom.map_pow (eval a), eval_X, eval_C,
    sub_self, finset.prod_eq_zero_iff],
  refine ⟨i, finset.mem_univ _, _⟩,
  rw [finite_field.pow_card_sub_one_eq_one, sub_self],
  rwa [(≠), sub_eq_zero],
end

lemma degrees_indicator (c : σ → K) :
  degrees (indicator c) ≤ ∑ s : σ, (fintype.card K - 1) • {s} :=
begin
  rw [indicator],
  refine le_trans (degrees_prod _ _) (finset.sum_le_sum $ assume s hs, _),
  refine le_trans (degrees_sub _ _) _,
  rw [degrees_one, ← bot_eq_zero, bot_sup_eq],
  refine le_trans (degrees_pow _ _) (nsmul_le_nsmul_of_le_right _ _),
  refine le_trans (degrees_sub _ _) _,
  rw [degrees_C, ← bot_eq_zero, sup_bot_eq],
  exact degrees_X' _
end

lemma indicator_mem_restrict_degree (c : σ → K) :
  indicator c ∈ restrict_degree σ K (fintype.card K - 1) :=
begin
  rw [mem_restrict_degree_iff_sup, indicator],
  assume n,
  refine le_trans (multiset.count_le_of_le _ $ degrees_indicator _) (le_of_eq _),
  rw [← finset.univ.sum_hom (multiset.count n)],
  simp only [is_add_monoid_hom.map_nsmul (multiset.count n), multiset.singleton_eq_singleton,
    nsmul_eq_mul, nat.cast_id],
  transitivity,
  refine finset.sum_eq_single n _ _,
  { assume b hb ne, rw [multiset.count_cons_of_ne ne.symm, multiset.count_zero, mul_zero] },
  { assume h, exact (h $ finset.mem_univ _).elim },
  { rw [multiset.count_cons_self, multiset.count_zero, mul_one] }
end

section
variables (K σ)
def evalₗ : mv_polynomial σ K →ₗ[K] (σ → K) → K :=
{ to_fun := λ p e, eval e p,
  map_add' := λ p q, by { ext x, rw ring_hom.map_add, refl, },
  map_smul' := λ a p, by { ext e, rw [smul_eq_C_mul, ring_hom.map_mul, eval_C], refl } }
end

lemma evalₗ_apply (p : mv_polynomial σ K) (e : σ → K) : evalₗ K σ p e = eval e p :=
rfl

lemma map_restrict_dom_evalₗ : (restrict_degree σ K (fintype.card K - 1)).map (evalₗ K σ) = ⊤ :=
begin
  refine top_unique (set_like.le_def.2 $ assume e _, mem_map.2 _),
  refine ⟨∑ n : σ → K, e n • indicator n, _, _⟩,
  { exact sum_mem _ (assume c _, smul_mem _ _ (indicator_mem_restrict_degree _)) },
  { ext n,
    simp only [linear_map.map_sum, @finset.sum_apply (σ → K) (λ_, K) _ _ _ _ _,
      pi.smul_apply, linear_map.map_smul],
    simp only [evalₗ_apply],
    transitivity,
    refine finset.sum_eq_single n _ _,
    { assume b _ h,
      rw [eval_indicator_apply_eq_zero _ _ h.symm, smul_zero] },
    { assume h, exact (h $ finset.mem_univ n).elim },
    { rw [eval_indicator_apply_eq_one, smul_eq_mul, mul_one] } }
end
end mv_polynomial

namespace mv_polynomial

open_locale classical
open linear_map submodule

universe u
variables (σ : Type u) (K : Type u) [fintype σ] [field K] [fintype K]

@[derive [add_comm_group, module K, inhabited]]
def R : Type u := restrict_degree σ K (fintype.card K - 1)

noncomputable instance decidable_restrict_degree (m : ℕ) :
  decidable_pred (∈ {n : σ →₀ ℕ | ∀i, n i ≤ m }) :=
by simp only [set.mem_set_of_eq]; apply_instance

lemma dim_R : module.rank K (R σ K) = fintype.card (σ → K) :=
calc module.rank K (R σ K) =
  module.rank K (↥{s : σ →₀ ℕ | ∀ (n : σ), s n ≤ fintype.card K - 1} →₀ K) :
    linear_equiv.dim_eq
      (finsupp.supported_equiv_finsupp {s : σ →₀ ℕ | ∀n:σ, s n ≤ fintype.card K - 1 })
  ... = cardinal.mk {s : σ →₀ ℕ | ∀ (n : σ), s n ≤ fintype.card K - 1} :
    by rw [finsupp.dim_eq, dim_of_field, mul_one]
  ... = cardinal.mk {s : σ → ℕ | ∀ (n : σ), s n < fintype.card K } :
  begin
    refine quotient.sound ⟨equiv.subtype_equiv finsupp.equiv_fun_on_fintype $ assume f, _⟩,
    refine forall_congr (assume n, nat.le_sub_right_iff_add_le _),
    exact fintype.card_pos_iff.2 ⟨0⟩
  end
  ... = cardinal.mk (σ → {n // n < fintype.card K}) :
    quotient.sound ⟨@equiv.subtype_pi_equiv_pi σ (λ_, ℕ) (λs n, n < fintype.card K)⟩
  ... = cardinal.mk (σ → fin (fintype.card K)) :
    quotient.sound ⟨equiv.arrow_congr (equiv.refl σ) (equiv.fin_equiv_subtype _).symm⟩
  ... = cardinal.mk (σ → K) :
    quotient.sound ⟨equiv.arrow_congr (equiv.refl σ) (fintype.equiv_fin K).symm⟩
  ... = fintype.card (σ → K) : cardinal.fintype_card _

instance : finite_dimensional K (R σ K) :=
is_noetherian.iff_dim_lt_omega.mpr
  (by simpa only [dim_R] using cardinal.nat_lt_omega (fintype.card (σ → K)))

lemma finrank_R : finite_dimensional.finrank K (R σ K) = fintype.card (σ → K) :=
finite_dimensional.finrank_eq_of_dim_eq (dim_R σ K)

def evalᵢ : R σ K →ₗ[K] (σ → K) → K :=
((evalₗ K σ).comp (restrict_degree σ K (fintype.card K - 1)).subtype)

lemma range_evalᵢ : (evalᵢ σ K).range = ⊤ :=
begin
  rw [evalᵢ, linear_map.range_comp, range_subtype],
  exact map_restrict_dom_evalₗ
end

lemma ker_evalₗ : (evalᵢ σ K).ker = ⊥ :=
begin
  refine (ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank _).mpr (range_evalᵢ _ _),
  rw [finite_dimensional.finrank_fintype_fun_eq_card, finrank_R]
end

lemma eq_zero_of_eval_eq_zero (p : mv_polynomial σ K)
  (h : ∀v:σ → K, eval v p = 0) (hp : p ∈ restrict_degree σ K (fintype.card K - 1)) :
  p = 0 :=
let p' : R σ K := ⟨p, hp⟩ in
have p' ∈ (evalᵢ σ K).ker := by { rw [mem_ker], ext v, exact h v },
show p'.1 = (0 : R σ K).1,
begin
  rw [ker_evalₗ, mem_bot] at this,
  rw [this]
end

end mv_polynomial
