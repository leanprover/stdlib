/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kenny Lau.
-/

import ring_theory.polynomial

/-!
# Lagrange interpolation

## Main definitions

* `lagrange.basis s x` where `s : finset F` and `x : F`: the Lagrange basis polynomial
  that evaluates to `1` at `x` and `0` at other elements of `s`.
* `lagrange.interpolate s f` where `s : finset F` and `f : s → F`: the Lagrange interpolant
  that evaluates to `f x` at `x` for `x ∈ s`.

-/

noncomputable theory
open_locale big_operators classical

universe u

namespace lagrange

variables {F : Type u} [decidable_eq F] [field F] (s : finset F)
variables {F' : Type u} [field F'] (s' : finset F')

open polynomial

/-- Lagrange basis polynomials that evaluate to 1 at `x` and 0 at other elements of `s`. -/
def basis (x : F) : polynomial F :=
∏ y in s.erase x, C (x - y)⁻¹ * (X - C y)

@[simp] theorem basis_empty (x : F) : basis ∅ x = 1 :=
rfl

@[simp] theorem eval_basis_self (x : F) : (basis s x).eval x = 1 :=
begin
  rw [basis, ← (s.erase x).prod_hom (eval x), finset.prod_eq_one],
  intros y hy, simp_rw [eval_mul, eval_sub, eval_C, eval_X],
  exact inv_mul_cancel (sub_ne_zero_of_ne (finset.ne_of_mem_erase hy).symm)
end

@[simp] theorem eval_basis_ne (x y : F) (h1 : y ∈ s) (h2 : y ≠ x) : (basis s x).eval y = 0 :=
begin
  rw [basis, ← (s.erase x).prod_hom (eval y), finset.prod_eq_zero (finset.mem_erase.2 ⟨h2, h1⟩)],
  simp_rw [eval_mul, eval_sub, eval_C, eval_X, sub_self, mul_zero]
end

theorem eval_basis (x y : F) (h : y ∈ s) : (basis s x).eval y = if y = x then 1 else 0 :=
by { split_ifs with H, { subst H, apply eval_basis_self }, { exact eval_basis_ne s x y h H } }

@[simp] theorem nat_degree_basis (x : F) (hx : x ∈ s) : (basis s x).nat_degree = s.card - 1 :=
begin
  unfold basis, generalize hsx : s.erase x = sx,
  have : x ∉ sx := hsx ▸ finset.not_mem_erase x s,
  rw [← finset.insert_erase hx, hsx, finset.card_insert_of_not_mem this, nat.add_sub_cancel],
  clear hx hsx s, revert this, apply sx.induction_on,
  { intros hx, rw [finset.prod_empty, nat_degree_one], refl },
  { intros y s hys ih hx, rw [finset.mem_insert, not_or_distrib] at hx,
    have h1 : C (x - y)⁻¹ ≠ C 0 := λ h, hx.1 (eq_of_sub_eq_zero $ inv_eq_zero.1 $ C_inj.1 h),
    have h2 : X ^ 1 - C y ≠ 0 := by convert X_pow_sub_C_ne_zero zero_lt_one y,
    rw C_0 at h1, rw pow_one at h2,
    rw [finset.prod_insert hys, nat_degree_mul (mul_ne_zero h1 h2), ih hx.2,
        finset.card_insert_of_not_mem hys, nat_degree_mul h1 h2,
        nat_degree_C, zero_add, nat_degree, degree_X_sub_C, add_comm], refl,
    rw [ne, finset.prod_eq_zero_iff], rintro ⟨z, hzs, hz⟩,
    rw mul_eq_zero at hz, cases hz with hz hz,
    { rw [← C_0, C_inj, inv_eq_zero, sub_eq_zero] at hz, exact hx.2 (hz.symm ▸ hzs) },
    { rw ← pow_one (X : polynomial F) at hz, exact X_pow_sub_C_ne_zero zero_lt_one _ hz } }
end

variables (f : (↑s : set F) → F)

/-- Lagrange interpolation: given a finset `s` and a function `f : s → F`,
`interpolate s f` is the unique polynomial of degree `< s.card`
that takes value `f x` on all `x` in `s`. -/
def interpolate : polynomial F :=
∑ x in s.attach, C (f x) * basis s x

@[simp] theorem interpolate_empty (f) : interpolate (∅ : finset F) f = 0 :=
rfl

@[simp] theorem eval_interpolate (x) (H : x ∈ s) : eval x (interpolate s f) = f ⟨x, H⟩ :=
begin
  rw [interpolate, ← finset.sum_hom _ (eval x), finset.sum_eq_single (⟨x, H⟩ : { x // x ∈ s })],
  { rw [eval_mul, eval_C, subtype.coe_mk, eval_basis_self, mul_one] },
  { rintros ⟨y, hy⟩ _ hyx, rw [eval_mul, subtype.coe_mk, eval_basis_ne s y x H, mul_zero],
    { rintros rfl, exact hyx rfl } },
  { intro h, exact absurd (finset.mem_attach _ _) h }
end

theorem degree_interpolate_lt : (interpolate s f).degree < s.card :=
if H : s = ∅ then by { subst H, rw [interpolate_empty, degree_zero], exact with_bot.bot_lt_coe _ }
else lt_of_le_of_lt (degree_sum_le _ _) $ (finset.sup_lt_iff $ with_bot.bot_lt_coe s.card).2 $ λ b _,
calc  (C (f b) * basis s b).degree
    ≤ (C (f b)).degree + (basis s b).degree : degree_mul_le _ _
... ≤ 0 + (basis s b).degree : add_le_add_right degree_C_le _
... = (basis s b).degree : zero_add _
... ≤ (basis s b).nat_degree : degree_le_nat_degree
... = (s.card - 1 : ℕ) : by { rw nat_degree_basis s b b.2 }
... < s.card : with_bot.coe_lt_coe.2 (nat.pred_lt $ mt finset.card_eq_zero.1 H)

/-- Linear version of `interpolate`. -/
def linterpolate : ((↑s : set F) → F) →ₗ[F] polynomial F :=
{ to_fun := interpolate s,
  map_add' := λ f g, by { simp_rw [interpolate, ← finset.sum_add_distrib, ← add_mul, ← C_add],
    refl },
  map_smul' := λ c f, by { simp_rw [interpolate, finset.smul_sum, C_mul', smul_smul], refl } }

@[simp] lemma interpolate_add (f g) : interpolate s (f + g) = interpolate s f + interpolate s g :=
(linterpolate s).map_add f g

@[simp] lemma interpolate_zero : interpolate s 0 = 0 :=
(linterpolate s).map_zero

@[simp] lemma interpolate_neg (f) : interpolate s (-f) = -interpolate s f :=
(linterpolate s).map_neg f

@[simp] lemma interpolate_sub (f g) : interpolate s (f - g) = interpolate s f - interpolate s g :=
(linterpolate s).map_sub f g

@[simp] lemma interpolate_smul (c : F) (f) : interpolate s (c • f) = c • interpolate s f :=
(linterpolate s).map_smul c f

theorem eq_zero_of_eval_eq_zero {f : polynomial F'} (hf1 : f.degree < s'.card)
  (hf2 : ∀ x ∈ s', f.eval x = 0) : f = 0 :=
by_contradiction $ λ hf3, not_le_of_lt hf1 $
calc  (s'.card : with_bot ℕ)
    ≤ f.roots.to_finset.card : with_bot.coe_le_coe.2 $ finset.card_le_of_subset $ λ x hx,
        (multiset.mem_to_finset).mpr $ (mem_roots hf3).2 $ hf2 x hx
... ≤ f.roots.card : with_bot.coe_le_coe.2 $ f.roots.to_finset_card_le
... ≤ f.degree : card_roots hf3

theorem eq_of_eval_eq {f g : polynomial F'} (hf : f.degree < s'.card) (hg : g.degree < s'.card)
  (hfg : ∀ x ∈ s', f.eval x = g.eval x) : f = g :=
eq_of_sub_eq_zero $ eq_zero_of_eval_eq_zero s'
  (lt_of_le_of_lt (degree_sub_le f g) $ max_lt hf hg)
  (λ x hx, by rw [eval_sub, hfg x hx, sub_self])

theorem eq_interpolate (f : polynomial F) (hf : f.degree < s.card) :
  interpolate s (λ x, f.eval x) = f :=
eq_of_eval_eq s (degree_interpolate_lt s _) hf $ λ x hx, eval_interpolate s _ x hx

/-- Lagrange interpolation induces isomorphism between functions from `s` and polynomials
of degree less than `s.card`. -/
def fun_equiv_degree_lt : degree_lt F s.card ≃ₗ[F] ((↑s : set F) → F) :=
{ to_fun := λ f x, f.1.eval x,
  map_add' := λ f g, funext $ λ x, eval_add,
  map_smul' := λ c f, funext $ λ x, by { rw [pi.smul_apply, smul_eq_mul, ← @eval_C F c _ x,
      ← eval_mul, eval_C, C_mul'], refl },
  inv_fun := λ f, ⟨interpolate s f, mem_degree_lt.2 $ degree_interpolate_lt s f⟩,
  left_inv := λ f, subtype.eq $ eq_interpolate s f $ mem_degree_lt.1 f.2,
  right_inv := λ f, funext $ λ ⟨x, hx⟩, eval_interpolate s f x hx }

end lagrange
