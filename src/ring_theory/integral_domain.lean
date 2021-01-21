/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes
-/

import data.polynomial.ring_division
import group_theory.order_of_element
import algebra.geom_sum

/-!
# Integral domains

Assorted theorems about integral domains.

## Main theorems

* `is_cyclic_of_subgroup_integral_domain` : A finite subgroup of the units of an integral domain
                                            is cyclic.
* `field_of_integral_domain`              : A finite integral domain is a field.

## Tags

integral domain, finite integral domain, finite field
-/

section

open finset polynomial function
open_locale big_operators nat

variables {R : Type*} {G : Type*} [integral_domain R] [group G] [fintype G]

lemma card_nth_roots_subgroup_units (f : G →* R) (hf : injective f) {n : ℕ} (hn : 0 < n) (g₀ : G) :
  ({g ∈ univ | g ^ n = g₀} : finset G).card ≤ (nth_roots n (f g₀)).card :=
begin
  haveI : decidable_eq R := classical.dec_eq _,
  refine le_trans _ (nth_roots n (f g₀)).to_finset_card_le,
  apply card_le_card_of_inj_on f,
  { intros g hg,
    rw [sep_def, mem_filter] at hg,
    rw [multiset.mem_to_finset, mem_nth_roots hn, ← f.map_pow, hg.2] },
  { intros, apply hf, assumption }
end

/-- A finite subgroup of the unit group of an integral domain is cyclic. -/
lemma is_cyclic_of_subgroup_integral_domain (f : G →* R) (hf : injective f) : is_cyclic G :=
begin
  haveI := classical.dec_eq G,
  apply is_cyclic_of_card_pow_eq_one_le,
  intros n hn,
  convert (le_trans (card_nth_roots_subgroup_units f hf hn 1) (card_nth_roots n (f 1)))
end

/-- The unit group of a finite integral domain is cyclic. -/
instance [fintype R] : is_cyclic (units R) :=
is_cyclic_of_subgroup_integral_domain (units.coe_hom R) $ units.ext

/-- Every finite integral domain is a field. -/
def field_of_integral_domain [decidable_eq R] [fintype R] : field R :=
{ inv := λ a, if h : a = 0 then 0
    else fintype.bij_inv (show function.bijective (* a),
      from fintype.injective_iff_bijective.1 $ λ _ _, mul_right_cancel' h) 1,
  mul_inv_cancel := λ a ha, show a * dite _ _ _ = _, by rw [dif_neg ha, mul_comm];
    exact fintype.right_inverse_bij_inv (show function.bijective (* a), from _) 1,
  inv_zero := dif_pos rfl,
  ..show integral_domain R, by apply_instance }

section

variables (S : set (units R)) [is_subgroup S] [fintype S]
local attribute [instance] subtype.group

/-- A finite subgroup of the units of an integral domain is cyclic. -/
instance subgroup_units_cyclic : is_cyclic S :=
begin
  refine is_cyclic_of_subgroup_integral_domain ⟨(coe : S → R), _, _⟩
    (units.ext.comp subtype.val_injective),
  { simp only [is_submonoid.coe_one, units.coe_one, coe_coe] },
  { intros, simp only [is_submonoid.coe_mul, units.coe_mul, coe_coe] },
end

end

lemma card_fiber_eq_of_mem_range {H : Type*} [group H] [decidable_eq H]
  (f : G →* H) {x y : H} (hx : x ∈ set.range f) (hy : y ∈ set.range f) :
  (univ.filter $ λ g, f g = x).card = (univ.filter $ λ g, f g = y).card :=
begin
  rcases hx with ⟨x, rfl⟩,
  rcases hy with ⟨y, rfl⟩,
  refine card_congr (λ g _, g * x⁻¹ * y) _ _ (λ g hg, ⟨g * y⁻¹ * x, _⟩),
  { simp only [mem_filter, one_mul, monoid_hom.map_mul, mem_univ, mul_right_inv,
      eq_self_iff_true, monoid_hom.map_mul_inv, and_self, forall_true_iff] {contextual := tt} },
  { simp only [mul_left_inj, imp_self, forall_2_true_iff], },
  { simp only [true_and, mem_filter, mem_univ] at hg,
    simp only [hg, mem_filter, one_mul, monoid_hom.map_mul, mem_univ, mul_right_inv,
      eq_self_iff_true, exists_prop_of_true, monoid_hom.map_mul_inv, and_self,
      mul_inv_cancel_right, inv_mul_cancel_right], }
end

section
local attribute [instance] subtype.group subtype.monoid range.is_submonoid
/-- In an integral domain, a sum indexed by a nontrivial homomorphism from a finite group is zero. -/
lemma sum_hom_units_eq_zero (f : G →* R) (hf : f ≠ 1) : ∑ g : G, f g = 0 :=
begin
  classical,
  obtain ⟨x, hx⟩ : ∃ x : set.range f.to_hom_units, ∀ y : set.range f.to_hom_units, y ∈ powers x,
    from is_cyclic.exists_monoid_generator (set.range (f.to_hom_units)),
  have hx1 : x ≠ 1,
  { rintro rfl,
    apply hf,
    ext g,
    rw [monoid_hom.one_apply],
    cases hx ⟨f.to_hom_units g, g, rfl⟩ with n hn,
    rwa [subtype.ext_iff, units.ext_iff, subtype.coe_mk, monoid_hom.coe_to_hom_units,
      is_submonoid.coe_pow, units.coe_pow, is_submonoid.coe_one, units.coe_one,
      one_pow, eq_comm] at hn, },
  replace hx1 : (x : R) - 1 ≠ 0,
    from λ h, hx1 (subtype.eq (units.ext (sub_eq_zero.1 h))),
  let c := (univ.filter (λ g, f.to_hom_units g = 1)).card,
  calc ∑ g : G, f g
      = ∑ g : G, f.to_hom_units g : rfl
  ... = ∑ u : units R in univ.image f.to_hom_units, (univ.filter (λ g, f.to_hom_units g = u)).card • u :
    sum_comp (coe : units R → R) f.to_hom_units
  ... = ∑ u : units R in univ.image f.to_hom_units, c • u :
    sum_congr rfl (λ u hu, congr_arg2 _ _ rfl) -- remaining goal 1, proven below
  ... = ∑ b : set.range f.to_hom_units, c • ↑b : finset.sum_subtype
      (by simp only [mem_image, set.mem_range, forall_const, iff_self, mem_univ, exists_prop_of_true]) _
  ... = c • ∑ b : set.range f.to_hom_units, (b : R) : smul_sum.symm
  ... = c • 0 : congr_arg2 _ rfl _            -- remaining goal 2, proven below
  ... = 0 : smul_zero _,
  { -- remaining goal 1
    show (univ.filter (λ (g : G), f.to_hom_units g = u)).card = c,
    apply card_fiber_eq_of_mem_range f.to_hom_units,
    { simpa only [mem_image, mem_univ, exists_prop_of_true, set.mem_range] using hu, },
    { exact ⟨1, f.to_hom_units.map_one⟩ } },
  -- remaining goal 2
  show ∑ b : set.range f.to_hom_units, (b : R) = 0,
  calc ∑ b : set.range f.to_hom_units, (b : R)
      = ∑ n in range (order_of x), x ^ n :
    eq.symm $ sum_bij (λ n _, x ^ n)
      (by simp only [mem_univ, forall_true_iff])
      (by simp only [is_submonoid.coe_pow, eq_self_iff_true, units.coe_pow, coe_coe, forall_true_iff])
      (λ m n hm hn, pow_injective_of_lt_order_of _
        (by simpa only [mem_range] using hm)
        (by simpa only [mem_range] using hn))
      (λ b hb, let ⟨n, hn⟩ := hx b in ⟨n % order_of x, mem_range.2 (nat.mod_lt _ (order_of_pos _)),
        by rw [← pow_eq_mod_order_of, hn]⟩)
  ... = 0 : _,
  rw [← mul_left_inj' hx1, zero_mul, ← geom_series, geom_sum_mul, coe_coe],
  norm_cast,
  rw [pow_order_of_eq_one, is_submonoid.coe_one, units.coe_one, sub_self],
end
end

/-- In an integral domain, a sum indexed by a homomorphism from a finite group is zero,
unless the homomorphism is trivial, in which case the sum is equal to the cardinality of the group. -/
lemma sum_hom_units (f : G →* R) [decidable (f = 1)] :
  ∑ g : G, f g = if f = 1 then fintype.card G else 0 :=
begin
  split_ifs with h h,
  { simp [h, card_univ] },
  { exact sum_hom_units_eq_zero f h }
end

end
