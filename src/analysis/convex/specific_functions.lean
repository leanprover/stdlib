/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
import analysis.calculus.mean_value
import data.nat.parity
import analysis.special_functions.pow

/-!
# Collection of convex functions

In this file we prove that the following functions are convex:

* `convex_on_exp` : the exponential function is convex on $(-∞, +∞)$;
* `convex_on_pow_of_even` : given an even natural number $n$, the function $f(x)=x^n$
  is convex on $(-∞, +∞)$;
* `convex_on_pow` : for a natural $n$, the function $f(x)=x^n$ is convex on $[0, +∞)$;
* `convex_on_fpow` : for an integer $m$, the function $f(x)=x^m$ is convex on $(0, +∞)$.
* `convex_on_rpow : ∀ p : ℝ, 1 ≤ p → convex_on (Ici 0) (λ x, x ^ p)`
* `concave_on_log_Ioi` and `concave_on_log_Iio`: log is concave on `Ioi 0` and `Iio 0` respectively.
-/

open real set
open_locale big_operators

/-- `exp` is convex on the whole real line -/
lemma convex_on_exp : convex_on univ exp :=
convex_on_univ_of_deriv2_nonneg differentiable_exp (by simp)
  (assume x, (iter_deriv_exp 2).symm ▸ le_of_lt (exp_pos x))

/-- `x^n`, `n : ℕ` is convex on the whole real line whenever `n` is even -/
lemma convex_on_pow_of_even {n : ℕ} (hn : even n) : convex_on set.univ (λ x : ℝ, x^n) :=
begin
  apply convex_on_univ_of_deriv2_nonneg differentiable_pow,
  { simp only [deriv_pow', differentiable.mul, differentiable_const, differentiable_pow] },
  { intro x,
    rcases nat.even.sub_even hn (nat.even_bit0 1) with ⟨k, hk⟩,
    simp only [iter_deriv_pow, finset.prod_range_succ, finset.prod_range_zero, nat.sub_zero,
      mul_one, hk, pow_mul', pow_two],
    exact mul_nonneg (nat.cast_nonneg _) (mul_self_nonneg _) }
end

/-- `x^n`, `n : ℕ` is convex on `[0, +∞)` for all `n` -/
lemma convex_on_pow (n : ℕ) : convex_on (Ici 0) (λ x : ℝ, x^n) :=
begin
  apply convex_on_of_deriv2_nonneg (convex_Ici _) (continuous_pow n).continuous_on;
    simp only [interior_Ici, differentiable_on_pow, deriv_pow',
      differentiable_on_const, differentiable_on.mul, iter_deriv_pow],
  intros x hx,
  exact mul_nonneg (nat.cast_nonneg _) (pow_nonneg (le_of_lt hx) _)
end

lemma finset.prod_nonneg_of_card_nonpos_even
  {α β : Type*} [linear_ordered_comm_ring β]
  {f : α → β} [decidable_pred (λ x, f x ≤ 0)]
  {s : finset α} (h0 : even (s.filter (λ x, f x ≤ 0)).card) :
  0 ≤ ∏ x in s, f x :=
calc 0 ≤ (∏ x in s, ((if f x ≤ 0 then (-1:β) else 1) * f x)) :
  finset.prod_nonneg (λ x _, by
    { split_ifs with hx hx, by simp [hx], simp at hx ⊢, exact le_of_lt hx })
... = _ : by rw [finset.prod_mul_distrib, finset.prod_ite, finset.prod_const_one,
  mul_one, finset.prod_const, neg_one_pow_eq_pow_mod_two, nat.even_iff.1 h0, pow_zero, one_mul]

lemma int_prod_range_nonneg (m : ℤ) (n : ℕ) (hn : even n) :
  0 ≤ ∏ k in finset.range n, (m - k) :=
begin
  cases (le_or_lt ↑n m) with hnm hmn,
  { exact finset.prod_nonneg (λ k hk, sub_nonneg.2 (le_trans
      (int.coe_nat_le.2 $ le_of_lt $ finset.mem_range.1 hk) hnm)) },
  cases le_or_lt 0 m with hm hm,
  { lift m to ℕ using hm,
    exact le_of_eq (eq.symm $ finset.prod_eq_zero
      (finset.mem_range.2 $ int.coe_nat_lt.1 hmn) (sub_self _)) },
  clear hmn,
  apply finset.prod_nonneg_of_card_nonpos_even,
  convert hn,
  convert finset.card_range n,
  ext k,
  simp only [finset.mem_filter, finset.mem_range],
  refine ⟨and.left, λ hk, ⟨hk, sub_nonpos.2 $ le_trans (le_of_lt hm) _⟩⟩,
  exact int.coe_nat_nonneg k
end

/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m` -/
lemma convex_on_fpow (m : ℤ) : convex_on (Ioi 0) (λ x : ℝ, x^m) :=
begin
  apply convex_on_open_of_deriv2_nonneg (convex_Ioi 0) (is_open_Ioi),
  { exact differentiable_on_fpow (lt_irrefl _) },
  { have : eq_on (deriv (λx:ℝ, x^m)) (λx, ↑m * x^(m-1)) (Ioi 0),
      from λ x hx, deriv_fpow,
    refine (differentiable_on_congr this).2 _,
    exact (differentiable_on_fpow (lt_irrefl _)).const_mul _ },
  { intros x hx,
    simp only [iter_deriv_fpow (ne_of_gt hx)],
    refine mul_nonneg (int.cast_nonneg.2 _) (fpow_nonneg (le_of_lt hx) _),
    exact int_prod_range_nonneg _ _ (nat.even_bit0 1) }
end

lemma convex_on_rpow {p : ℝ} (hp : 1 ≤ p) : convex_on (Ici 0) (λ x : ℝ, x^p) :=
begin
  have A : deriv (λ (x : ℝ), x ^ p) = λ x, p * x^(p-1), by { ext x, simp [hp] },
  apply convex_on_of_deriv2_nonneg (convex_Ici 0),
  { apply (continuous_rpow_of_pos (λ _, lt_of_lt_of_le zero_lt_one hp)
      continuous_id continuous_const).continuous_on },
  { apply differentiable.differentiable_on, simp [hp] },
  { rw A,
    assume x hx,
    replace hx : x ≠ 0, by { simp at hx, exact ne_of_gt hx },
    simp [differentiable_at.differentiable_within_at, hx] },
  { assume x hx,
    replace hx : 0 < x, by simpa using hx,
    suffices : 0 ≤ p * ((p - 1) * x ^ (p - 1 - 1)), by simpa [ne_of_gt hx, A],
    apply mul_nonneg (le_trans zero_le_one hp),
    exact mul_nonneg (sub_nonneg_of_le hp) (rpow_nonneg_of_nonneg (le_of_lt hx) _) }
end

lemma concave_on_log_Ioi : concave_on (Ioi 0) log :=
begin
  have h₁ : Ioi 0 ⊆ ({0} : set ℝ)ᶜ,
  { intros x hx hx',
    rw [mem_singleton_iff] at hx',
    rw [hx'] at hx,
    exact lt_irrefl 0 hx },
  refine concave_on_open_of_deriv2_nonpos (convex_Ioi 0) is_open_Ioi _ _ _,
  { exact differentiable_on_log.mono h₁ },
  { refine ((times_cont_diff_on_log.deriv_of_open _ le_top).differentiable_on le_top).mono h₁,
    exact is_open_compl_singleton },
  { intros x hx,
    simp [function.iterate_succ, function.iterate_one, pow_two_nonneg x] }
end

lemma concave_on_log_Iio : concave_on (Iio 0) log :=
begin
  have h₁ : Iio 0 ⊆ ({0} : set ℝ)ᶜ,
  { intros x hx hx',
    rw [mem_singleton_iff] at hx',
    rw [hx'] at hx,
    exact lt_irrefl 0 hx },
  refine concave_on_open_of_deriv2_nonpos (convex_Iio 0) is_open_Iio _ _ _,
  { exact differentiable_on_log.mono h₁ },
  { refine ((times_cont_diff_on_log.deriv_of_open _ le_top).differentiable_on le_top).mono h₁,
    exact is_open_compl_singleton },
  { intros x hx,
    simp [function.iterate_succ, function.iterate_one, pow_two_nonneg x] }
end
