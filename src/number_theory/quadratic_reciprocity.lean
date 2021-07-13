/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import field_theory.finite.basic
import data.zmod.basic
import data.nat.parity

/-!
# Quadratic reciprocity.

This file contains results about quadratic residues modulo a prime number.

The main results are the law of quadratic reciprocity, `quadratic_reciprocity`, as well as the
interpretations in terms of existence of square roots depending on the congruence mod 4,
`exists_sq_eq_prime_iff_of_mod_four_eq_one`, and
`exists_sq_eq_prime_iff_of_mod_four_eq_three`.

Also proven are conditions for `-1` and `2` to be a square modulo a prime,
`exists_sq_eq_neg_one_iff_mod_four_ne_three` and
`exists_sq_eq_two_iff`

## Implementation notes

The proof of quadratic reciprocity implemented uses Gauss' lemma and Eisenstein's lemma
-/

open function finset nat finite_field zmod
open_locale big_operators nat

namespace zmod

variables (p q : ℕ) [fact p.prime] [fact q.prime]

/-- Euler's Criterion: A unit `x` of `zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
lemma euler_criterion_units (x : units (zmod p)) :
  (∃ y : units (zmod p), y ^ 2 = x) ↔ x ^ (p / 2) = 1 :=
begin
  cases nat.prime.eq_two_or_odd (fact.out p.prime) with hp2 hp_odd,
  { substI p, refine iff_of_true ⟨1, _⟩ _; apply subsingleton.elim  },
  obtain ⟨g, hg⟩ := is_cyclic.exists_generator (units (zmod p)),
  obtain ⟨n, hn⟩ : x ∈ submonoid.powers g, { rw mem_powers_iff_mem_gpowers, apply hg },
  split,
  { rintro ⟨y, rfl⟩, rw [← pow_mul, two_mul_odd_div_two hp_odd, units_pow_card_sub_one_eq_one], },
  { subst x, assume h,
    have key : 2 * (p / 2) ∣ n * (p / 2),
    { rw [← pow_mul] at h,
      rw [two_mul_odd_div_two hp_odd, ← card_units, ← order_of_eq_card_of_forall_mem_gpowers hg],
      apply order_of_dvd_of_pow_eq_one h },
    have : 0 < p / 2 := nat.div_pos (fact.out (1 < p)) dec_trivial,
    obtain ⟨m, rfl⟩ := dvd_of_mul_dvd_mul_right this key,
    refine ⟨g ^ m, _⟩,
    rw [mul_comm, pow_mul], },
end

/-- Euler's Criterion: a nonzero `a : zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
lemma euler_criterion {a : zmod p} (ha : a ≠ 0) :
  (∃ y : zmod p, y ^ 2 = a) ↔ a ^ (p / 2) = 1 :=
begin
  apply (iff_congr _ (by simp [units.ext_iff])).mp (euler_criterion_units p (units.mk0 a ha)),
  simp only [units.ext_iff, sq, units.coe_mk0, units.coe_mul],
  split, { rintro ⟨y, hy⟩, exact ⟨y, hy⟩ },
  { rintro ⟨y, rfl⟩,
    have hy : y ≠ 0, { rintro rfl, simpa [zero_pow] using ha, },
    refine ⟨units.mk0 y hy, _⟩, simp, }
end

lemma exists_sq_eq_neg_one_iff_mod_four_ne_three :
  (∃ y : zmod p, y ^ 2 = -1) ↔ p % 4 ≠ 3 :=
begin
  cases nat.prime.eq_two_or_odd (fact.out p.prime) with hp2 hp_odd,
  { substI p, exact dec_trivial },
  haveI := fact.mk hp_odd,
  have neg_one_ne_zero : (-1 : zmod p) ≠ 0, from mt neg_eq_zero.1 one_ne_zero,
  rw [euler_criterion p neg_one_ne_zero, neg_one_pow_eq_pow_mod_two],
  cases mod_two_eq_zero_or_one (p / 2) with p_half_even p_half_odd,
  { rw [p_half_even, pow_zero, eq_self_iff_true, true_iff],
    contrapose! p_half_even with hp,
    rw [← nat.mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hp],
    exact dec_trivial },
  { rw [p_half_odd, pow_one,
        iff_false_intro (ne_neg_self p one_ne_zero).symm, false_iff, not_not],
    rw [← nat.mod_mul_right_div_self, show 2 * 2 = 4, from rfl] at p_half_odd,
    rw [← nat.mod_mul_left_mod _ 2, show 2 * 2 = 4, from rfl] at hp_odd,
    have hp : p % 4 < 4, from nat.mod_lt _ dec_trivial,
    revert hp hp_odd p_half_odd,
    generalize : p % 4 = k, dec_trivial! }
end

lemma pow_div_two_eq_neg_one_or_one {a : zmod p} (ha : a ≠ 0) :
  a ^ (p / 2) = 1 ∨ a ^ (p / 2) = -1 :=
begin
  cases nat.prime.eq_two_or_odd (fact.out p.prime) with hp2 hp_odd,
  { substI p, revert a ha, exact dec_trivial },
  rw [← mul_self_eq_one_iff, ← pow_add, ← two_mul, two_mul_odd_div_two hp_odd],
  exact pow_card_sub_one_eq_one ha
end

/-- **Wilson's Lemma**: the product of `1`, ..., `p-1` is `-1` modulo `p`. -/
@[simp] lemma wilsons_lemma : ((p - 1)! : zmod p) = -1 :=
begin
  refine
  calc ((p - 1)! : zmod p) = (∏ x in Ico 1 (succ (p - 1)), x) :
    by rw [← finset.prod_Ico_id_eq_factorial, prod_nat_cast]
                               ... = (∏ x : units (zmod p), x) : _
                               ... = -1 :
    by rw [prod_hom _ (coe : units (zmod p) → zmod p),
           prod_univ_units_id_eq_neg_one, units.coe_neg, units.coe_one],
  have hp : 0 < p := (fact.out p.prime).pos,
  symmetry,
  refine prod_bij (λ a _, (a : zmod p).val) _ _ _ _,
  { intros a ha,
    rw [Ico.mem, ← nat.succ_sub hp, nat.succ_sub_one],
    split,
    { apply nat.pos_of_ne_zero, rw ← @val_zero p,
      assume h, apply units.ne_zero a (val_injective p h) },
    { exact val_lt _ } },
  { intros a ha, simp only [cast_id, nat_cast_val], },
  { intros _ _ _ _ h, rw units.ext_iff, exact val_injective p h },
  { intros b hb,
    rw [Ico.mem, nat.succ_le_iff, ← succ_sub hp, succ_sub_one, pos_iff_ne_zero] at hb,
    refine ⟨units.mk0 b _, finset.mem_univ _, _⟩,
    { assume h, apply hb.1, apply_fun val at h,
      simpa only [val_cast_of_lt hb.right, val_zero] using h },
    { simp only [val_cast_of_lt hb.right, units.coe_mk0], } }
end

@[simp] lemma prod_Ico_one_prime : (∏ x in Ico 1 p, (x : zmod p)) = -1 :=
begin
  conv in (Ico 1 p) { rw [← succ_sub_one p, succ_sub (fact.out p.prime).pos] },
  rw [← prod_nat_cast, finset.prod_Ico_id_eq_factorial, wilsons_lemma]
end

end zmod

/-- The image of the map sending a non zero natural number `x ≤ p / 2` to the absolute value
  of the element of interger in the interval `(-p/2, p/2]` congruent to `a * x` mod p is the set
  of non zero natural numbers `x` such that `x ≤ p / 2` -/
lemma Ico_map_val_min_abs_nat_abs_eq_Ico_map_id
  (p : ℕ) [hp : fact p.prime] (a : zmod p) (hap : a ≠ 0) :
  (Ico 1 (p / 2).succ).1.map (λ x, (a * x).val_min_abs.nat_abs) =
  (Ico 1 (p / 2).succ).1.map (λ a, a) :=
begin
  have he : ∀ {x}, x ∈ Ico 1 (p / 2).succ → x ≠ 0 ∧ x ≤ p / 2,
    by simp [nat.lt_succ_iff, nat.succ_le_iff, pos_iff_ne_zero] {contextual := tt},
  have hep : ∀ {x}, x ∈ Ico 1 (p / 2).succ → x < p,
    from λ x hx, lt_of_le_of_lt (he hx).2 (nat.div_lt_self hp.1.pos dec_trivial),
  have hpe : ∀ {x}, x ∈ Ico 1 (p / 2).succ → ¬ p ∣ x,
    from λ x hx hpx, not_lt_of_ge (le_of_dvd (nat.pos_of_ne_zero (he hx).1) hpx) (hep hx),
  have hmem : ∀ (x : ℕ) (hx : x ∈ Ico 1 (p / 2).succ),
    (a * x : zmod p).val_min_abs.nat_abs ∈ Ico 1 (p / 2).succ,
  { assume x hx,
    simp [hap, char_p.cast_eq_zero_iff (zmod p) p, hpe hx, lt_succ_iff, succ_le_iff,
        pos_iff_ne_zero, nat_abs_val_min_abs_le _], },
  have hsurj : ∀ (b : ℕ) (hb : b ∈ Ico 1 (p / 2).succ),
    ∃ x ∈ Ico 1 (p / 2).succ, b = (a * x : zmod p).val_min_abs.nat_abs,
  { assume b hb,
    refine ⟨(b / a : zmod p).val_min_abs.nat_abs, Ico.mem.mpr ⟨_, _⟩, _⟩,
    { apply nat.pos_of_ne_zero,
      simp only [div_eq_mul_inv, hap, char_p.cast_eq_zero_iff (zmod p) p, hpe hb, not_false_iff,
        val_min_abs_eq_zero, inv_eq_zero, int.nat_abs_eq_zero, ne.def, mul_eq_zero, or_self] },
      { apply lt_succ_of_le, apply nat_abs_val_min_abs_le },
      { rw nat_cast_nat_abs_val_min_abs,
        split_ifs,
        { erw [mul_div_cancel' _ hap, val_min_abs_def_pos, val_cast_of_lt (hep hb),
            if_pos (le_of_lt_succ (Ico.mem.1 hb).2), int.nat_abs_of_nat], },
        { erw [mul_neg_eq_neg_mul_symm, mul_div_cancel' _ hap, nat_abs_val_min_abs_neg,
            val_min_abs_def_pos, val_cast_of_lt (hep hb), if_pos (le_of_lt_succ (Ico.mem.1 hb).2),
            int.nat_abs_of_nat] } } },
  exact multiset.map_eq_map_of_bij_of_nodup _ _ (finset.nodup _) (finset.nodup _)
    (λ x _, (a * x : zmod p).val_min_abs.nat_abs) hmem (λ _ _, rfl)
    (inj_on_of_surj_on_of_card_le _ hmem hsurj (le_refl _)) hsurj
end

private lemma gauss_lemma_aux₁ (p : ℕ) [fact p.prime] [fact (p % 2 = 1)]
  {a : ℕ} (hap : (a : zmod p) ≠ 0) :
  (a^(p / 2) * (p / 2)! : zmod p) =
  (-1)^((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, ¬(a * x : zmod p).val ≤ p / 2)).card * (p / 2)! :=
calc (a ^ (p / 2) * (p / 2)! : zmod p) =
    (∏ x in Ico 1 (p / 2).succ, a * x) :
  by rw [prod_mul_distrib, ← prod_nat_cast, ← prod_nat_cast, prod_Ico_id_eq_factorial,
      prod_const, Ico.card, succ_sub_one]; simp
... = (∏ x in Ico 1 (p / 2).succ, (a * x : zmod p).val) : by simp
... = (∏ x in Ico 1 (p / 2).succ,
    (if (a * x : zmod p).val ≤ p / 2 then 1 else -1) *
      (a * x : zmod p).val_min_abs.nat_abs) :
  prod_congr rfl $ λ _ _, begin
    simp only [nat_cast_nat_abs_val_min_abs],
    split_ifs; simp
  end
... = (-1)^((Ico 1 (p / 2).succ).filter
      (λ x : ℕ, ¬(a * x : zmod p).val ≤ p / 2)).card *
    (∏ x in Ico 1 (p / 2).succ, (a * x : zmod p).val_min_abs.nat_abs) :
  have (∏ x in Ico 1 (p / 2).succ,
        if (a * x : zmod p).val ≤ p / 2 then (1 : zmod p) else -1) =
      (∏ x in (Ico 1 (p / 2).succ).filter
        (λ x : ℕ, ¬(a * x : zmod p).val ≤ p / 2), -1),
    from prod_bij_ne_one (λ x _ _, x)
      (λ x, by split_ifs; simp * at * {contextual := tt})
      (λ _ _ _ _ _ _, id)
      (λ b h _, ⟨b, by simp [-not_le, *] at *⟩)
      (by intros; split_ifs at *; simp * at *),
  by rw [prod_mul_distrib, this]; simp
... = (-1)^((Ico 1 (p / 2).succ).filter
      (λ x : ℕ, ¬(a * x : zmod p).val ≤ p / 2)).card * (p / 2)! :
  by rw [← prod_nat_cast, finset.prod_eq_multiset_prod,
      Ico_map_val_min_abs_nat_abs_eq_Ico_map_id p a hap,
      ← finset.prod_eq_multiset_prod, prod_Ico_id_eq_factorial]

private lemma gauss_lemma_aux₂ (p : ℕ) [hp : fact p.prime] [fact (p % 2 = 1)]
  {a : ℕ} (hap : (a : zmod p) ≠ 0) :
  (a^(p / 2) : zmod p) = (-1)^((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card :=
(mul_left_inj'
    (show ((p / 2)! : zmod p) ≠ 0,
      by rw [ne.def, char_p.cast_eq_zero_iff (zmod p) p, hp.1.dvd_factorial, not_le];
          exact nat.div_lt_self hp.1.pos dec_trivial)).1 $
  by simpa using gauss_lemma_aux₁ p hap

private lemma eisenstein_lemma_aux₁ (p : ℕ) [fact p.prime] [hp2 : fact (p % 2 = 1)]
  {a : ℕ} (hap : (a : zmod p) ≠ 0) :
  ((∑ x in Ico 1 (p / 2).succ, a * x : ℕ) : zmod 2) =
    ((Ico 1 (p / 2).succ).filter
      ((λ x : ℕ, p / 2 < (a * x : zmod p).val))).card +
      ∑ x in Ico 1 (p / 2).succ, x
    + (∑ x in Ico 1 (p / 2).succ, (a * x) / p : ℕ) :=
have hp2 : (p : zmod 2) = (1 : ℕ), from (eq_iff_modeq_nat _).2 hp2.1,
calc ((∑ x in Ico 1 (p / 2).succ, a * x : ℕ) : zmod 2)
    = ((∑ x in Ico 1 (p / 2).succ, ((a * x) % p + p * ((a * x) / p)) : ℕ) : zmod 2) :
  by simp only [mod_add_div]
... = (∑ x in Ico 1 (p / 2).succ, ((a * x : ℕ) : zmod p).val : ℕ) +
    (∑ x in Ico 1 (p / 2).succ, (a * x) / p : ℕ) :
  by simp only [val_nat_cast];
    simp [sum_add_distrib, mul_sum.symm, nat.cast_add, nat.cast_mul, nat.cast_sum, hp2]
... = _ : congr_arg2 (+)
  (calc ((∑ x in Ico 1 (p / 2).succ, ((a * x : ℕ) : zmod p).val : ℕ) : zmod 2)
      = ∑ x in Ico 1 (p / 2).succ,
          ((((a * x : zmod p).val_min_abs +
            (if (a * x : zmod p).val ≤ p / 2 then 0 else p)) : ℤ) : zmod 2) :
        by simp only [(val_eq_ite_val_min_abs _).symm]; simp [nat.cast_sum]
  ... = ((Ico 1 (p / 2).succ).filter
        (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card +
      ((∑ x in Ico 1 (p / 2).succ, (a * x : zmod p).val_min_abs.nat_abs) : ℕ) :
    by { simp [ite_cast, add_comm, sum_add_distrib, finset.sum_ite, hp2, nat.cast_sum], }
  ... = _ : by rw [finset.sum_eq_multiset_sum,
      Ico_map_val_min_abs_nat_abs_eq_Ico_map_id p a hap,
      ← finset.sum_eq_multiset_sum];
    simp [nat.cast_sum]) rfl

private lemma eisenstein_lemma_aux₂ (p : ℕ) [fact p.prime] [fact (p % 2 = 1)]
  {a : ℕ} (ha2 : a % 2 = 1) (hap : (a : zmod p) ≠ 0) :
  ((Ico 1 (p / 2).succ).filter
    ((λ x : ℕ, p / 2 < (a * x : zmod p).val))).card
  ≡ ∑ x in Ico 1 (p / 2).succ, (x * a) / p [MOD 2] :=
have ha2 : (a : zmod 2) = (1 : ℕ), from (eq_iff_modeq_nat _).2 ha2,
(eq_iff_modeq_nat 2).1 $ sub_eq_zero.1 $
  by simpa [add_left_comm, sub_eq_add_neg, finset.mul_sum.symm, mul_comm, ha2, nat.cast_sum,
            add_neg_eq_iff_eq_add.symm, neg_eq_self_mod_two, add_assoc]
    using eq.symm (eisenstein_lemma_aux₁ p hap)

lemma div_eq_filter_card {a b c : ℕ} (hb0 : 0 < b) (hc : a / b ≤ c) : a / b =
  ((Ico 1 c.succ).filter (λ x, x * b ≤ a)).card :=
calc a / b = (Ico 1 (a / b).succ).card : by simp
... = ((Ico 1 c.succ).filter (λ x, x * b ≤ a)).card :
  congr_arg _ $ finset.ext $ λ x,
    have x * b ≤ a → x ≤ c,
      from λ h, le_trans (by rwa [le_div_iff_mul_le _ _ hb0]) hc,
    by simp [lt_succ_iff, le_div_iff_mul_le _ _ hb0]; tauto

/-- The given sum is the number of integer points in the triangle formed by the diagonal of the
  rectangle `(0, p/2) × (0, q/2)`  -/
private lemma sum_Ico_eq_card_lt {p q : ℕ} :
  ∑ a in Ico 1 (p / 2).succ, (a * q) / p =
  (((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)).filter
  (λ x : ℕ × ℕ, x.2 * p ≤ x.1 * q)).card :=
if hp0 : p = 0 then by simp [hp0, finset.ext_iff]
else
  calc ∑ a in Ico 1 (p / 2).succ, (a * q) / p =
    ∑ a in Ico 1 (p / 2).succ,
      ((Ico 1 (q / 2).succ).filter (λ x, x * p ≤ a * q)).card :
    finset.sum_congr rfl $ λ x hx,
      div_eq_filter_card (nat.pos_of_ne_zero hp0)
        (calc x * q / p ≤ (p / 2) * q / p :
            nat.div_le_div_right (mul_le_mul_of_nonneg_right
              (le_of_lt_succ $ by finish)
              (nat.zero_le _))
          ... ≤ _ : nat.div_mul_div_le_div _ _ _)
  ... = _ : by rw [← card_sigma];
    exact card_congr (λ a _, ⟨a.1, a.2⟩)
      (by simp only [mem_filter, mem_sigma, and_self, forall_true_iff, mem_product]
        {contextual := tt})
      (λ ⟨_, _⟩ ⟨_, _⟩, by simp only [prod.mk.inj_iff, eq_self_iff_true, and_self, heq_iff_eq,
        forall_true_iff] {contextual := tt})
      (λ ⟨b₁, b₂⟩ h, ⟨⟨b₁, b₂⟩,
        by revert h; simp only [mem_filter, eq_self_iff_true, exists_prop_of_true, mem_sigma,
          and_self, forall_true_iff, mem_product] {contextual := tt}⟩)

/-- Each of the sums in this lemma is the cardinality of the set integer points in each of the
  two triangles formed by the diagonal of the rectangle `(0, p/2) × (0, q/2)`. Adding them
  gives the number of points in the rectangle. -/
private lemma sum_mul_div_add_sum_mul_div_eq_mul (p q : ℕ) [hp : fact p.prime]
  (hq0 : (q : zmod p) ≠ 0) :
  ∑ a in Ico 1 (p / 2).succ, (a * q) / p +
  ∑ a in Ico 1 (q / 2).succ, (a * p) / q =
  (p / 2) * (q / 2) :=
begin
  have hswap : (((Ico 1 (q / 2).succ).product (Ico 1 (p / 2).succ)).filter
    (λ x : ℕ × ℕ, x.2 * q ≤ x.1 * p)).card =
  (((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)).filter
    (λ x : ℕ × ℕ, x.1 * q ≤ x.2 * p)).card :=
  card_congr (λ x _, prod.swap x)
    (λ ⟨_, _⟩, by simp only [mem_filter, and_self, prod.swap_prod_mk, forall_true_iff, mem_product]
      {contextual := tt})
    (λ ⟨_, _⟩ ⟨_, _⟩, by simp only [prod.mk.inj_iff, eq_self_iff_true, and_self, prod.swap_prod_mk,
      forall_true_iff] {contextual := tt})
    (λ ⟨x₁, x₂⟩ h, ⟨⟨x₂, x₁⟩, by revert h; simp only [mem_filter, eq_self_iff_true, and_self,
      exists_prop_of_true, prod.swap_prod_mk, forall_true_iff, mem_product] {contextual := tt}⟩),
  have hdisj : disjoint
    (((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)).filter
      (λ x : ℕ × ℕ, x.2 * p ≤ x.1 * q))
    (((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)).filter
      (λ x : ℕ × ℕ, x.1 * q ≤ x.2 * p)),
  { apply disjoint_filter.2 (λ x hx hpq hqp, _),
    have hxp : x.1 < p, from lt_of_le_of_lt
      (show x.1 ≤ p / 2, by simp only [*, lt_succ_iff, Ico.mem, mem_product] at *; tauto)
      (nat.div_lt_self hp.1.pos dec_trivial),
    have : (x.1 : zmod p) = 0,
      { simpa [hq0] using congr_arg (coe : ℕ → zmod p) (le_antisymm hpq hqp) },
    apply_fun zmod.val at this,
    rw [val_cast_of_lt hxp, val_zero] at this,
    simpa only [this, nonpos_iff_eq_zero, Ico.mem, one_ne_zero, false_and, mem_product] using hx },
  have hunion : ((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)).filter
      (λ x : ℕ × ℕ, x.2 * p ≤ x.1 * q) ∪
    ((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)).filter
      (λ x : ℕ × ℕ, x.1 * q ≤ x.2 * p) =
    ((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)),
  from finset.ext (λ x, by have := le_total (x.2 * p) (x.1 * q);
    simp only [mem_union, mem_filter, Ico.mem, mem_product]; tauto),
  rw [sum_Ico_eq_card_lt, sum_Ico_eq_card_lt, hswap, ← card_disjoint_union hdisj, hunion,
    card_product],
  simp only [Ico.card, nat.sub_zero, succ_sub_succ_eq_sub]
end

variables (p q : ℕ) [fact p.prime] [fact q.prime]

namespace zmod

/-- The Legendre symbol of `a` and `p` is an integer defined as

* `0` if `a` is `0` modulo `p`;
* `1` if `a ^ (p / 2)` is `1` modulo `p`
   (by `euler_criterion` this is equivalent to “`a` is a square modulo `p`”);
* `-1` otherwise.

-/
def legendre_sym (a p : ℕ) : ℤ :=
if      (a : zmod p) = 0           then  0
else if (a : zmod p) ^ (p / 2) = 1 then  1
                                   else -1

lemma legendre_sym_eq_pow (a p : ℕ) [hp : fact p.prime] :
  (legendre_sym a p : zmod p) = (a ^ (p / 2)) :=
begin
  rw legendre_sym,
  by_cases ha : (a : zmod p) = 0,
  { simp only [if_pos, ha, zero_pow (nat.div_pos (hp.1.two_le) (succ_pos 1)), int.cast_zero] },
  cases hp.1.eq_two_or_odd with hp2 hp_odd,
  { substI p,
    generalize : (a : (zmod 2)) = b, revert b, dec_trivial, },
  { haveI := fact.mk hp_odd,
    rw if_neg ha,
    have : (-1 : zmod p) ≠ 1, from (ne_neg_self p one_ne_zero).symm,
    cases pow_div_two_eq_neg_one_or_one p ha with h h,
    { rw [if_pos h, h, int.cast_one], },
    { rw [h, if_neg this, int.cast_neg, int.cast_one], } }
end

lemma legendre_sym_eq_one_or_neg_one (a p : ℕ) (ha : (a : zmod p) ≠ 0) :
  legendre_sym a p = -1 ∨ legendre_sym a p = 1 :=
by unfold legendre_sym; split_ifs; simp only [*, eq_self_iff_true, or_true, true_or] at *

lemma legendre_sym_eq_zero_iff (a p : ℕ) :
  legendre_sym a p = 0 ↔ (a : zmod p) = 0 :=
begin
  split,
  { classical, contrapose,
    assume ha, cases legendre_sym_eq_one_or_neg_one a p ha with h h,
    all_goals { rw h, norm_num } },
  { assume ha, rw [legendre_sym, if_pos ha] }
end

/-- Gauss' lemma. The legendre symbol can be computed by considering the number of naturals less
  than `p/2` such that `(a * x) % p > p / 2` -/
lemma gauss_lemma {a : ℕ} [fact (p % 2 = 1)] (ha0 : (a : zmod p) ≠ 0) :
  legendre_sym a p = (-1) ^ ((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card :=
have (legendre_sym a p : zmod p) = (((-1)^((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card : ℤ) : zmod p),
  by rw [legendre_sym_eq_pow, gauss_lemma_aux₂ p ha0]; simp,
begin
  cases legendre_sym_eq_one_or_neg_one a p ha0;
  cases neg_one_pow_eq_or ℤ ((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card;
  simp [*, ne_neg_self p one_ne_zero, (ne_neg_self p one_ne_zero).symm] at *
end

lemma legendre_sym_eq_one_iff {a : ℕ} (ha0 : (a : zmod p) ≠ 0) :
  legendre_sym a p = 1 ↔ (∃ b : zmod p, b ^ 2 = a) :=
begin
  rw [euler_criterion p ha0, legendre_sym, if_neg ha0],
  split_ifs,
  { simp only [h, eq_self_iff_true] },
  finish -- this is quite slow. I'm actually surprised that it can close the goal at all!
end

lemma eisenstein_lemma [fact (p % 2 = 1)] {a : ℕ} (ha1 : a % 2 = 1) (ha0 : (a : zmod p) ≠ 0) :
  legendre_sym a p = (-1)^∑ x in Ico 1 (p / 2).succ, (x * a) / p :=
by rw [neg_one_pow_eq_pow_mod_two, gauss_lemma p ha0, neg_one_pow_eq_pow_mod_two,
    show _ = _, from eisenstein_lemma_aux₂ p ha1 ha0]

/-- **Quadratic reciprocity theorem** -/
theorem quadratic_reciprocity [hp1 : fact (p % 2 = 1)] [hq1 : fact (q % 2 = 1)] (hpq : p ≠ q) :
  legendre_sym p q * legendre_sym q p = (-1) ^ ((p / 2) * (q / 2)) :=
have hpq0 : (p : zmod q) ≠ 0, from prime_ne_zero q p hpq.symm,
have hqp0 : (q : zmod p) ≠ 0, from prime_ne_zero p q hpq,
by rw [eisenstein_lemma q hp1.1 hpq0, eisenstein_lemma p hq1.1 hqp0,
  ← pow_add, sum_mul_div_add_sum_mul_div_eq_mul q p hpq0, mul_comm]

-- move this
local attribute [instance]
lemma fact_prime_two : fact (nat.prime 2) := ⟨nat.prime_two⟩

lemma legendre_sym_two [hp1 : fact (p % 2 = 1)] : legendre_sym 2 p = (-1) ^ (p / 4 + p / 2) :=
have hp2 : p ≠ 2, from mt (congr_arg (% 2)) (by simpa using hp1.1),
have hp22 : p / 2 / 2 = _ := div_eq_filter_card (show 0 < 2, from dec_trivial)
  (nat.div_le_self (p / 2) 2),
have hcard : (Ico 1 (p / 2).succ).card = p / 2, by simp,
have hx2 : ∀ x ∈ Ico 1 (p / 2).succ, (2 * x : zmod p).val = 2 * x,
  from λ x hx, have h2xp : 2 * x < p,
      from calc 2 * x ≤ 2 * (p / 2) : mul_le_mul_of_nonneg_left
        (le_of_lt_succ $ by finish) dec_trivial
      ... < _ : by conv_rhs {rw [← div_add_mod p 2, hp1.1]}; exact lt_succ_self _,
    by rw [← nat.cast_two, ← nat.cast_mul, val_cast_of_lt h2xp],
have hdisj : disjoint
    ((Ico 1 (p / 2).succ).filter (λ x, p / 2 < ((2 : ℕ) * x : zmod p).val))
    ((Ico 1 (p / 2).succ).filter (λ x, x * 2 ≤ p / 2)),
  from disjoint_filter.2 (λ x hx, by simp [hx2 _ hx, mul_comm]),
have hunion :
    ((Ico 1 (p / 2).succ).filter (λ x, p / 2 < ((2 : ℕ) * x : zmod p).val)) ∪
    ((Ico 1 (p / 2).succ).filter (λ x, x * 2 ≤ p / 2)) =
    Ico 1 (p / 2).succ,
  begin
    rw [filter_union_right],
    conv_rhs {rw [← @filter_true _ (Ico 1 (p / 2).succ)]},
    exact filter_congr (λ x hx, by simp [hx2 _ hx, lt_or_le, mul_comm])
  end,
begin
  rw [gauss_lemma p (prime_ne_zero p 2 hp2),
    neg_one_pow_eq_pow_mod_two, @neg_one_pow_eq_pow_mod_two _ _ (p / 4 + p / 2)],
  refine congr_arg2 _ rfl ((eq_iff_modeq_nat 2).1 _),
  rw [show 4 = 2 * 2, from rfl, ← nat.div_div_eq_div_mul, hp22, nat.cast_add,
    ← sub_eq_iff_eq_add', sub_eq_add_neg, neg_eq_self_mod_two,
    ← nat.cast_add, ← card_disjoint_union hdisj, hunion, hcard]
end

lemma exists_sq_eq_two_iff [hp1 : fact (p % 2 = 1)] :
  (∃ a : zmod p, a ^ 2 = 2) ↔ p % 8 = 1 ∨ p % 8 = 7 :=
have hp2 : ((2 : ℕ) : zmod p) ≠ 0,
  from prime_ne_zero p 2 (λ h, by simpa [h] using hp1.1),
have hpm4 : p % 4 = p % 8 % 4, from (nat.mod_mul_left_mod p 2 4).symm,
have hpm2 : p % 2 = p % 8 % 2, from (nat.mod_mul_left_mod p 4 2).symm,
begin
  rw [show (2 : zmod p) = (2 : ℕ), by simp, ← legendre_sym_eq_one_iff p hp2,
    legendre_sym_two p, neg_one_pow_eq_one_iff_even (show (-1 : ℤ) ≠ 1, from dec_trivial),
    even_add, even_div, even_div],
  have := nat.mod_lt p (show 0 < 8, from dec_trivial),
  resetI, rw fact_iff at hp1,
  revert this hp1,
  erw [hpm4, hpm2],
  generalize hm : p % 8 = m, unfreezingI {clear_dependent p},
  dec_trivial!,
end

lemma exists_sq_eq_prime_iff_of_mod_four_eq_one (hp1 : p % 4 = 1) [hq1 : fact (q % 2 = 1)] :
  (∃ a : zmod p, a ^ 2 = q) ↔ ∃ b : zmod q, b ^ 2 = p :=
if hpq : p = q then by substI hpq else
have h1 : ((p / 2) * (q / 2)) % 2 = 0,
  from (dvd_iff_mod_eq_zero _ _).1
    (dvd_mul_of_dvd_left ((dvd_iff_mod_eq_zero _ _).2 $
    by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hp1]; refl) _),
begin
  haveI hp_odd : fact (p % 2 = 1) := ⟨odd_of_mod_four_eq_one hp1⟩,
  have hpq0 : (p : zmod q) ≠ 0 := prime_ne_zero q p (ne.symm hpq),
  have hqp0 : (q : zmod p) ≠ 0 := prime_ne_zero p q hpq,
  have := quadratic_reciprocity p q hpq,
  rw [neg_one_pow_eq_pow_mod_two, h1, legendre_sym, legendre_sym,
    if_neg hqp0, if_neg hpq0] at this,
  rw [euler_criterion q hpq0, euler_criterion p hqp0],
  split_ifs at this; simp *; contradiction,
end

lemma exists_sq_eq_prime_iff_of_mod_four_eq_three (hp3 : p % 4 = 3)
  (hq3 : q % 4 = 3) (hpq : p ≠ q) : (∃ a : zmod p, a ^ 2 = q) ↔ ¬∃ b : zmod q, b ^ 2 = p :=
have h1 : ((p / 2) * (q / 2)) % 2 = 1,
  from nat.odd_mul_odd
    (by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hp3]; refl)
    (by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hq3]; refl),
begin
  haveI hp_odd : fact (p % 2 = 1) := ⟨odd_of_mod_four_eq_three hp3⟩,
  haveI hq_odd : fact (q % 2 = 1) := ⟨odd_of_mod_four_eq_three hq3⟩,
  have hpq0 : (p : zmod q) ≠ 0 := prime_ne_zero q p (ne.symm hpq),
  have hqp0 : (q : zmod p) ≠ 0 := prime_ne_zero p q hpq,
  have := quadratic_reciprocity p q hpq,
  rw [neg_one_pow_eq_pow_mod_two, h1, legendre_sym, legendre_sym,
    if_neg hpq0, if_neg hqp0] at this,
  rw [euler_criterion q hpq0, euler_criterion p hqp0],
  split_ifs at this; simp *; contradiction
end

end zmod
