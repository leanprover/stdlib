/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import set_theory.cardinal_ordinal
import analysis.specific_limits
import data.rat.denumerable
import data.set.intervals.image_preimage

/-!
# The cardinality of the reals

This file shows that the real numbers have cardinality continuum, i.e. `#ℝ = 2^ω`.

We shows that `#ℝ ≤ 2^ω` by noting that every real number is determined by a Cauchy-sequence of the
form `ℕ → ℚ`, which has cardinality `2^ω`. To show that `#ℝ ≥ 2^ω` we define an injection from
`{0, 1} ^ ℕ` to `ℝ` with `f ↦ Σ n, f n * (1 / 3) ^ n`.

We conclude that all intervals with distinct endpoints have cardinality continuum.

## Main definitions

* `cardinal.cantor_function` is the function that sends `f` in `{0, 1} ^ ℕ` to `ℝ` by
  `f ↦ Σ' n, f n * (1 / 3) ^ n`

## Main statements

* `cardinal.mk_real : #ℝ = 2 ^ omega`: the reals have cardinality continuum.
* `cardinal.not_countable_real`: the universal set of real numbers is not countable.
  We can use this same proof to show that all the other sets in this file are not countable.
* 8 lemmas of the form `mk_Ixy_real` for `x,y ∈ {i,o,c}` state that intervals on the reals
  have cardinality continuum.

## Tags
continuum, cardinality, reals, cardinality of the reals
-/

open nat set
open_locale cardinal
noncomputable theory

namespace cardinal

variables {c : ℝ} {f g : ℕ → bool} {n : ℕ}

/-- The body of the sum in `cantor_function`.
`cantor_function_aux c f n = c ^ n` if `f n = tt`;
`cantor_function_aux c f n = 0` if `f n = ff`. -/
def cantor_function_aux (c : ℝ) (f : ℕ → bool) (n : ℕ) : ℝ := cond (f n) (c ^ n) 0

@[simp] lemma cantor_function_aux_tt (h : f n = tt) : cantor_function_aux c f n = c ^ n :=
by simp [cantor_function_aux, h]

@[simp] lemma cantor_function_aux_ff (h : f n = ff) : cantor_function_aux c f n = 0 :=
by simp [cantor_function_aux, h]

lemma cantor_function_aux_nonneg (h : 0 ≤ c) : 0 ≤ cantor_function_aux c f n :=
by { cases h' : f n; simp [h'], apply pow_nonneg h }

lemma cantor_function_aux_eq (h : f n = g n) :
  cantor_function_aux c f n = cantor_function_aux c g n :=
by simp [cantor_function_aux, h]

lemma cantor_function_aux_succ (f : ℕ → bool) :
  (λ n, cantor_function_aux c f (n + 1)) = λ n, c * cantor_function_aux c (λ n, f (n + 1)) n :=
by { ext n, cases h : f (n + 1); simp [h, pow_succ] }

lemma summable_cantor_function (f : ℕ → bool) (h1 : 0 ≤ c) (h2 : c < 1) :
  summable (cantor_function_aux c f) :=
begin
  apply (summable_geometric_of_lt_1 h1 h2).summable_of_eq_zero_or_self,
  intro n, cases h : f n; simp [h]
end

/-- `cantor_function c (f : ℕ → bool)` is `Σ n, f n * c ^ n`, where `tt` is interpreted as `1` and
`ff` is interpreted as `0`. It is implemented using `cantor_function_aux`. -/
def cantor_function (c : ℝ) (f : ℕ → bool) : ℝ := ∑' n, cantor_function_aux c f n

lemma cantor_function_le (h1 : 0 ≤ c) (h2 : c < 1) (h3 : ∀ n, f n → g n) :
  cantor_function c f ≤ cantor_function c g :=
begin
  apply tsum_le_tsum _ (summable_cantor_function f h1 h2) (summable_cantor_function g h1 h2),
  intro n, cases h : f n, simp [h, cantor_function_aux_nonneg h1],
  replace h3 : g n = tt := h3 n h, simp [h, h3]
end

lemma cantor_function_succ (f : ℕ → bool) (h1 : 0 ≤ c) (h2 : c < 1) :
  cantor_function c f = cond (f 0) 1 0 + c * cantor_function c (λ n, f (n+1)) :=
begin
  rw [cantor_function, tsum_eq_zero_add (summable_cantor_function f h1 h2)],
  rw [cantor_function_aux_succ, tsum_mul_left, cantor_function_aux, pow_zero],
  refl
end

/-- `cantor_function c` is strictly increasing with if `0 < c < 1/2`, if we endow `ℕ → bool` with a
lexicographic order. The lexicographic order doesn't exist for these infinitary products, so we
explicitly write out what it means. -/
lemma increasing_cantor_function (h1 : 0 < c) (h2 : c < 1 / 2) {n : ℕ} {f g : ℕ → bool}
  (hn : ∀(k < n), f k = g k) (fn : f n = ff) (gn : g n = tt) :
  cantor_function c f < cantor_function c g :=
begin
  have h3 : c < 1, { apply h2.trans, norm_num },
  induction n with n ih generalizing f g,
  { let f_max : ℕ → bool := λ n, nat.rec ff (λ _ _, tt) n,
    have hf_max : ∀n, f n → f_max n,
    { intros n hn, cases n, rw [fn] at hn, contradiction, apply rfl },
    let g_min : ℕ → bool := λ n, nat.rec tt (λ _ _, ff) n,
    have hg_min : ∀n, g_min n → g n,
    { intros n hn, cases n, rw [gn], apply rfl, contradiction },
    apply (cantor_function_le (le_of_lt h1) h3 hf_max).trans_lt,
    refine lt_of_lt_of_le _ (cantor_function_le (le_of_lt h1) h3 hg_min),
    have : c / (1 - c) < 1,
    { rw [div_lt_one, lt_sub_iff_add_lt],
      { convert add_lt_add h2 h2, norm_num },
      rwa sub_pos },
    convert this,
    { rw [cantor_function_succ _ (le_of_lt h1) h3, div_eq_mul_inv,
          ←tsum_geometric_of_lt_1 (le_of_lt h1) h3],
      apply zero_add },
    { convert tsum_eq_single 0 _,
      { apply_instance },
      { intros n hn, cases n, contradiction, refl } } },
  rw [cantor_function_succ f (le_of_lt h1) h3, cantor_function_succ g (le_of_lt h1) h3],
  rw [hn 0 $ zero_lt_succ n],
  apply add_lt_add_left, rw mul_lt_mul_left h1, exact ih (λ k hk, hn _ $ succ_lt_succ hk) fn gn
end

/-- `cantor_function c` is injective if `0 < c < 1/2`. -/
lemma cantor_function_injective (h1 : 0 < c) (h2 : c < 1 / 2) :
  function.injective (cantor_function c) :=
begin
  intros f g hfg, classical, by_contra h, revert hfg,
  have : ∃n, f n ≠ g n,
  { rw [←not_forall], intro h', apply h, ext, apply h' },
  let n := nat.find this,
  have hn : ∀ (k : ℕ), k < n → f k = g k,
  { intros k hk, apply of_not_not, exact nat.find_min this hk },
  cases fn : f n,
  { apply ne_of_lt, refine increasing_cantor_function h1 h2 hn fn _,
    apply eq_tt_of_not_eq_ff, rw [←fn], apply ne.symm, exact nat.find_spec this },
  { apply ne_of_gt, refine increasing_cantor_function h1 h2 (λ k hk, (hn k hk).symm) _ fn,
    apply eq_ff_of_not_eq_tt, rw [←fn], apply ne.symm, exact nat.find_spec this }
end

/-- The cardinality of the reals, as a type. -/
lemma mk_real : #ℝ = 2 ^ omega.{0} :=
begin
  apply le_antisymm,
  { rw real.equiv_Cauchy.cardinal_eq,
    apply mk_quotient_le.trans, apply (mk_subtype_le _).trans,
    rw [←power_def, mk_nat, mk_rat, power_self_eq (le_refl _)] },
  { convert mk_le_of_injective (cantor_function_injective _ _),
    rw [←power_def, mk_bool, mk_nat], exact 1 / 3, norm_num, norm_num }
end

/-- The cardinality of the reals, as a set. -/
lemma mk_univ_real : #(set.univ : set ℝ) = 2 ^ omega.{0} :=
by rw [mk_univ, mk_real]

/-- **Non-Denumerability of the Continuum**: The reals are not countable. -/
lemma not_countable_real : ¬ countable (set.univ : set ℝ) :=
by { rw [countable_iff, not_le, mk_univ_real], apply cantor }

/-- The cardinality of the interval (a, ∞). -/
lemma mk_Ioi_real (a : ℝ) : #(Ioi a) = 2 ^ omega.{0} :=
begin
  refine le_antisymm (mk_real ▸ mk_set_le _) _,
  rw [← not_lt], intro h,
  refine ne_of_lt _ mk_univ_real,
  have hu : Iio a ∪ {a} ∪ Ioi a = set.univ,
  { convert Iic_union_Ioi, exact Iio_union_right },
  rw ← hu,
  refine lt_of_le_of_lt (mk_union_le _ _) _,
  refine lt_of_le_of_lt (add_le_add_right (mk_union_le _ _) _) _,
  have h2 : (λ x, a + a - x) '' Ioi a = Iio a,
  { convert image_const_sub_Ioi _ _, simp },
  rw ← h2,
  refine add_lt_of_lt (cantor _).le _ h,
  refine add_lt_of_lt (cantor _).le (mk_image_le.trans_lt h) _,
  rw mk_singleton,
  exact one_lt_omega.trans (cantor _)
end

/-- The cardinality of the interval [a, ∞). -/
lemma mk_Ici_real (a : ℝ) : #(Ici a) = 2 ^ omega.{0} :=
le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioi_real a ▸ mk_le_mk_of_subset Ioi_subset_Ici_self)

/-- The cardinality of the interval (-∞, a). -/
lemma mk_Iio_real (a : ℝ) : #(Iio a) = 2 ^ omega.{0} :=
begin
  refine le_antisymm (mk_real ▸ mk_set_le _) _,
  have h2 : (λ x, a + a - x) '' Iio a = Ioi a,
  { convert image_const_sub_Iio _ _, simp },
  exact mk_Ioi_real a ▸ h2 ▸ mk_image_le
end

/-- The cardinality of the interval (-∞, a]. -/
lemma mk_Iic_real (a : ℝ) : #(Iic a) = 2 ^ omega.{0} :=
le_antisymm (mk_real ▸ mk_set_le _) (mk_Iio_real a ▸ mk_le_mk_of_subset Iio_subset_Iic_self)

/-- The cardinality of the interval (a, b). -/
lemma mk_Ioo_real {a b : ℝ} (h : a < b) : #(Ioo a b) = 2 ^ omega.{0} :=
begin
  refine le_antisymm (mk_real ▸ mk_set_le _) _,
  have h1 : #((λ x, x - a) '' Ioo a b) ≤ #(Ioo a b) := mk_image_le,
  refine le_trans _ h1,
  rw [image_sub_const_Ioo, sub_self],
  replace h := sub_pos_of_lt h,
  have h2 : #(has_inv.inv '' Ioo 0 (b - a)) ≤ #(Ioo 0 (b - a)) := mk_image_le,
  refine le_trans _ h2,
  rw [image_inv_Ioo_0_left h, mk_Ioi_real]
end

/-- The cardinality of the interval [a, b). -/
lemma mk_Ico_real {a b : ℝ} (h : a < b) : #(Ico a b) = 2 ^ omega.{0} :=
le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Ico_self)

/-- The cardinality of the interval [a, b]. -/
lemma mk_Icc_real {a b : ℝ} (h : a < b) : #(Icc a b) = 2 ^ omega.{0} :=
le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Icc_self)

/-- The cardinality of the interval (a, b]. -/
lemma mk_Ioc_real {a b : ℝ} (h : a < b) : #(Ioc a b) = 2 ^ omega.{0} :=
le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Ioc_self)

end cardinal
